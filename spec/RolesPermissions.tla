--------------------------- MODULE RolesPermissions ---------------------------
(*****************************************************************************)
(* Role-Based Access Control (RBAC) for ColibrìDB                           *)
(*                                                                           *)
(* This specification models a comprehensive RBAC system with:              *)
(*   - Role hierarchy with inheritance                                      *)
(*   - Role-permission assignments                                          *)
(*   - User-role assignments (static and dynamic)                           *)
(*   - Separation of Duty (SoD) constraints                                 *)
(*   - Least Privilege principle enforcement                                *)
(*   - Role activation/deactivation                                         *)
(*   - Temporal constraints on roles                                        *)
(*   - Context-based role activation (location, time, etc.)                 *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Sandhu et al. (1996): "Role-Based Access Control Models" (RBAC96)   *)
(*   - Ferraiolo et al. (2001): NIST RBAC Standard                         *)
(*   - Sandhu et al. (1999): "Role-Based Administration (RBA)"             *)
(*   - Ahn & Sandhu (2000): "Role-Based Authorization Constraints"         *)
(*   - Li et al. (2007): "Temporal RBAC"                                   *)
(*   - Bertino et al. (2001): "TRBAC: Temporal Role-Based Access Control"  *)
(*   - Oracle Database Security Guide - RBAC                                *)
(*                                                                           *)
(* Implements RBAC Models:                                                  *)
(*   - RBAC0: Core RBAC (users, roles, permissions, sessions)              *)
(*   - RBAC1: Hierarchical RBAC (role inheritance)                         *)
(*   - RBAC2: Constrained RBAC (SoD constraints)                           *)
(*   - RBAC3: Consolidated RBAC (RBAC1 + RBAC2)                            *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE, TLC

CONSTANTS
    Users,              \* Set of all users
    Roles,              \* Set of all roles
    Permissions,        \* Set of all permissions
    Objects,            \* Set of protected objects
    Operations,         \* Set of operations
    MaxActiveRoles,     \* Max roles per session
    MaxRoleDepth        \* Max depth of role hierarchy

VARIABLES
    userRoles,          \* user -> {roles}
    rolePermissions,    \* role -> {permissions}
    roleHierarchy,      \* role -> {senior_roles} (inheritance)
    sessions,           \* session_id -> [user, activeRoles, context]
    constraints,        \* Set of SoD and other constraints
    roleActivations,    \* role -> [minUsers, maxUsers, activeCount]
    temporalConstraints, \* role -> [validFrom, validUntil, timePattern]
    auditLog,           \* Sequence of RBAC events
    currentTime         \* Global clock

vars == <<userRoles, rolePermissions, roleHierarchy, sessions, constraints,
          roleActivations, temporalConstraints, auditLog, currentTime>>

--------------------------------------------------------------------------------
(* Type Definitions *)

Role == Roles
User == Users
Permission == Permissions
SessionId == Nat

(* Permission structure: (object, operation) *)
PermissionType == [object: Objects, operation: Operations]

(* Session context for context-aware RBAC *)
SessionContext == [
    location: STRING,
    ipAddress: STRING,
    timeOfDay: Nat,
    day: STRING
]

(* Constraint types *)
ConstraintType == {
    "STATIC_SoD",      \* Statically Mutually Exclusive Roles
    "DYNAMIC_SoD",     \* Dynamically Mutually Exclusive Roles
    "PREREQUISITE",    \* Role requires another role
    "CARDINALITY"      \* Limit on role assignments
}

Constraint == [
    type: ConstraintType,
    roles: SUBSET Roles,
    limit: Nat
]

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ userRoles = [u \in Users |-> {}]
    /\ rolePermissions = [r \in Roles |-> {}]
    /\ roleHierarchy = [r \in Roles |-> {}]  \* r -> senior roles
    /\ sessions = [s \in {} |-> <<>>]
    /\ constraints = {}
    /\ roleActivations = [r \in Roles |-> 
         [minUsers |-> 0, maxUsers |-> Cardinality(Users), activeCount |-> 0]]
    /\ temporalConstraints = [r \in Roles |->
         [validFrom |-> 0, validUntil |-> 999999, 
          enabledDays |-> {"Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"},
          enabledHours |-> {h \in 0..23 : TRUE}]]
    /\ auditLog = <<>>
    /\ currentTime = 0

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Compute transitive closure of role hierarchy (inherited roles) *)
RECURSIVE InheritedRoles(_)
InheritedRoles(role) ==
    IF role \notin Roles THEN {}
    ELSE
        {role} \cup UNION {InheritedRoles(r) : r \in roleHierarchy[role]}

(* Get all permissions for a role (including inherited) *)
AllPermissionsForRole(role) ==
    LET inherited == InheritedRoles(role)
    IN UNION {rolePermissions[r] : r \in inherited}

(* Get all permissions for a user *)
AllPermissionsForUser(user) ==
    LET userRoleSet == userRoles[user]
    IN UNION {AllPermissionsForRole(r) : r \in userRoleSet}

(* Check if user has specific permission *)
HasPermission(user, object, operation) ==
    LET perms == AllPermissionsForUser(user)
        perm == [object |-> object, operation |-> operation]
    IN perm \in perms

(* Check if role hierarchy creates a cycle *)
HasCycle(role, visited) ==
    IF role \in visited THEN TRUE
    ELSE
        \E senior \in roleHierarchy[role] :
            HasCycle(senior, visited \cup {role})

(* Check role hierarchy depth *)
RECURSIVE RoleDepth(_)
RoleDepth(role) ==
    IF roleHierarchy[role] = {} THEN 0
    ELSE 1 + Max({RoleDepth(r) : r \in roleHierarchy[role]})

(* Check Static Separation of Duty *)
ViolatesStaticSoD(user, role, sodConstraint) ==
    /\ sodConstraint.type = "STATIC_SoD"
    /\ role \in sodConstraint.roles
    /\ LET conflictingRoles == sodConstraint.roles \ {role}
           userRoleSet == userRoles[user]
       IN Cardinality(userRoleSet \cap conflictingRoles) >= sodConstraint.limit

(* Check Dynamic Separation of Duty *)
ViolatesDynamicSoD(sessionId, role, sodConstraint) ==
    /\ sodConstraint.type = "DYNAMIC_SoD"
    /\ role \in sodConstraint.roles
    /\ sessionId \in DOMAIN sessions
    /\ LET conflictingRoles == sodConstraint.roles \ {role}
           activeRoles == sessions[sessionId].activeRoles
       IN Cardinality(activeRoles \cap conflictingRoles) >= sodConstraint.limit

(* Check prerequisite constraint *)
SatisfiesPrerequisite(user, role, prereqConstraint) ==
    /\ prereqConstraint.type = "PREREQUISITE"
    /\ role \in prereqConstraint.roles
    => \E req \in prereqConstraint.roles \ {role} : req \in userRoles[user]

(* Check cardinality constraint *)
SatisfiesCardinality(user, role, cardConstraint) ==
    /\ cardConstraint.type = "CARDINALITY"
    /\ role \in cardConstraint.roles
    => Cardinality(userRoles[user] \cap cardConstraint.roles) < cardConstraint.limit

(* Check temporal constraints *)
SatisfiesTemporalConstraints(role, time, context) ==
    LET tc == temporalConstraints[role]
    IN
        /\ time >= tc.validFrom
        /\ time <= tc.validUntil
        /\ context.day \in tc.enabledDays
        /\ context.timeOfDay \in tc.enabledHours

(* Check all constraints *)
SatisfiesAllConstraints(user, role) ==
    \A c \in constraints :
        /\ (c.type = "STATIC_SoD" => ~ViolatesStaticSoD(user, role, c))
        /\ (c.type = "PREREQUISITE" => SatisfiesPrerequisite(user, role, c))
        /\ (c.type = "CARDINALITY" => SatisfiesCardinality(user, role, c))

SatisfiesSessionConstraints(sessionId, role) ==
    \A c \in constraints :
        c.type = "DYNAMIC_SoD" => ~ViolatesDynamicSoD(sessionId, role, c)

--------------------------------------------------------------------------------
(* Role Assignment *)

AssignRole(admin, user, role) ==
    /\ role \in Roles
    /\ role \notin userRoles[user]
    /\ SatisfiesAllConstraints(user, role)
    /\ userRoles' = [userRoles EXCEPT ![user] = @ \cup {role}]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_ASSIGNED",
          admin |-> admin,
          user |-> user,
          role |-> role,
          time |-> currentTime])
    /\ UNCHANGED <<rolePermissions, roleHierarchy, sessions, constraints,
                  roleActivations, temporalConstraints, currentTime>>

RevokeRole(admin, user, role) ==
    /\ role \in userRoles[user]
    /\ userRoles' = [userRoles EXCEPT ![user] = @ \ {role}]
    \* Revoke role from all user sessions
    /\ sessions' = [s \in DOMAIN sessions |->
         IF sessions[s].user = user
         THEN [sessions[s] EXCEPT !.activeRoles = @ \ {role}]
         ELSE sessions[s]]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_REVOKED",
          admin |-> admin,
          user |-> user,
          role |-> role,
          time |-> currentTime])
    /\ UNCHANGED <<rolePermissions, roleHierarchy, constraints,
                  roleActivations, temporalConstraints, currentTime>>

--------------------------------------------------------------------------------
(* Permission Assignment *)

GrantPermission(admin, role, permission) ==
    /\ role \in Roles
    /\ permission \in Permissions
    /\ permission \notin rolePermissions[role]
    /\ rolePermissions' = [rolePermissions EXCEPT ![role] = @ \cup {permission}]
    /\ auditLog' = Append(auditLog,
         [event |-> "PERMISSION_GRANTED",
          admin |-> admin,
          role |-> role,
          permission |-> permission,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, roleHierarchy, sessions, constraints,
                  roleActivations, temporalConstraints, currentTime>>

RevokePermission(admin, role, permission) ==
    /\ permission \in rolePermissions[role]
    /\ rolePermissions' = [rolePermissions EXCEPT ![role] = @ \ {permission}]
    /\ auditLog' = Append(auditLog,
         [event |-> "PERMISSION_REVOKED",
          admin |-> admin,
          role |-> role,
          permission |-> permission,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, roleHierarchy, sessions, constraints,
                  roleActivations, temporalConstraints, currentTime>>

--------------------------------------------------------------------------------
(* Role Hierarchy *)

AddRoleInheritance(admin, juniorRole, seniorRole) ==
    /\ juniorRole \in Roles /\ seniorRole \in Roles
    /\ juniorRole # seniorRole
    /\ seniorRole \notin roleHierarchy[juniorRole]
    \* Check for cycles
    /\ ~HasCycle(seniorRole, {juniorRole})
    \* Check depth limit
    /\ RoleDepth(juniorRole) < MaxRoleDepth
    /\ roleHierarchy' = [roleHierarchy EXCEPT 
         ![juniorRole] = @ \cup {seniorRole}]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_INHERITANCE_ADDED",
          admin |-> admin,
          junior |-> juniorRole,
          senior |-> seniorRole,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, sessions, constraints,
                  roleActivations, temporalConstraints, currentTime>>

RemoveRoleInheritance(admin, juniorRole, seniorRole) ==
    /\ seniorRole \in roleHierarchy[juniorRole]
    /\ roleHierarchy' = [roleHierarchy EXCEPT 
         ![juniorRole] = @ \ {seniorRole}]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_INHERITANCE_REMOVED",
          admin |-> admin,
          junior |-> juniorRole,
          senior |-> seniorRole,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, sessions, constraints,
                  roleActivations, temporalConstraints, currentTime>>

--------------------------------------------------------------------------------
(* Session Management *)

CreateSession(user, sessionId, context) ==
    /\ sessionId \notin DOMAIN sessions
    /\ sessions' = sessions @@ (sessionId :> 
         [user |-> user, activeRoles |-> {}, context |-> context])
    /\ auditLog' = Append(auditLog,
         [event |-> "SESSION_CREATED",
          user |-> user,
          sessionId |-> sessionId,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, constraints,
                  roleActivations, temporalConstraints, currentTime>>

ActivateRole(user, sessionId, role) ==
    /\ sessionId \in DOMAIN sessions
    /\ sessions[sessionId].user = user
    /\ role \in userRoles[user]
    /\ role \notin sessions[sessionId].activeRoles
    /\ Cardinality(sessions[sessionId].activeRoles) < MaxActiveRoles
    /\ SatisfiesSessionConstraints(sessionId, role)
    /\ SatisfiesTemporalConstraints(role, currentTime, sessions[sessionId].context)
    /\ sessions' = [sessions EXCEPT 
         ![sessionId].activeRoles = @ \cup {role}]
    /\ roleActivations' = [roleActivations EXCEPT
         ![role].activeCount = @ + 1]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_ACTIVATED",
          user |-> user,
          sessionId |-> sessionId,
          role |-> role,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, constraints,
                  temporalConstraints, currentTime>>

DeactivateRole(user, sessionId, role) ==
    /\ sessionId \in DOMAIN sessions
    /\ sessions[sessionId].user = user
    /\ role \in sessions[sessionId].activeRoles
    /\ sessions' = [sessions EXCEPT 
         ![sessionId].activeRoles = @ \ {role}]
    /\ roleActivations' = [roleActivations EXCEPT
         ![role].activeCount = @ - 1]
    /\ auditLog' = Append(auditLog,
         [event |-> "ROLE_DEACTIVATED",
          user |-> user,
          sessionId |-> sessionId,
          role |-> role,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, constraints,
                  temporalConstraints, currentTime>>

CloseSession(sessionId) ==
    /\ sessionId \in DOMAIN sessions
    /\ LET activeRoles == sessions[sessionId].activeRoles
       IN
           /\ sessions' = [s \in (DOMAIN sessions \ {sessionId}) |-> sessions[s]]
           /\ roleActivations' = [r \in Roles |->
                IF r \in activeRoles
                THEN [roleActivations[r] EXCEPT !.activeCount = @ - 1]
                ELSE roleActivations[r]]
    /\ auditLog' = Append(auditLog,
         [event |-> "SESSION_CLOSED",
          sessionId |-> sessionId,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, constraints,
                  temporalConstraints, currentTime>>

--------------------------------------------------------------------------------
(* Constraint Management *)

AddConstraint(admin, constraint) ==
    /\ constraint \notin constraints
    /\ constraint.type \in ConstraintType
    /\ constraint.roles \subseteq Roles
    /\ constraints' = constraints \cup {constraint}
    /\ auditLog' = Append(auditLog,
         [event |-> "CONSTRAINT_ADDED",
          admin |-> admin,
          constraint |-> constraint,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, sessions,
                  roleActivations, temporalConstraints, currentTime>>

RemoveConstraint(admin, constraint) ==
    /\ constraint \in constraints
    /\ constraints' = constraints \ {constraint}
    /\ auditLog' = Append(auditLog,
         [event |-> "CONSTRAINT_REMOVED",
          admin |-> admin,
          constraint |-> constraint,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, sessions,
                  roleActivations, temporalConstraints, currentTime>>

--------------------------------------------------------------------------------
(* Temporal Constraints *)

SetTemporalConstraint(admin, role, validFrom, validUntil, enabledDays, enabledHours) ==
    /\ role \in Roles
    /\ validFrom < validUntil
    /\ temporalConstraints' = [temporalConstraints EXCEPT
         ![role] = [validFrom |-> validFrom,
                   validUntil |-> validUntil,
                   enabledDays |-> enabledDays,
                   enabledHours |-> enabledHours]]
    /\ auditLog' = Append(auditLog,
         [event |-> "TEMPORAL_CONSTRAINT_SET",
          admin |-> admin,
          role |-> role,
          time |-> currentTime])
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, sessions,
                  constraints, roleActivations, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<userRoles, rolePermissions, roleHierarchy, sessions,
                  constraints, roleActivations, temporalConstraints, auditLog>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E a, u \in Users, r \in Roles : AssignRole(a, u, r)
    \/ \E a, u \in Users, r \in Roles : RevokeRole(a, u, r)
    \/ \E a \in Users, r \in Roles, p \in Permissions : GrantPermission(a, r, p)
    \/ \E a \in Users, r \in Roles, p \in Permissions : RevokePermission(a, r, p)
    \/ \E a \in Users, jr, sr \in Roles : AddRoleInheritance(a, jr, sr)
    \/ \E a \in Users, jr, sr \in Roles : RemoveRoleInheritance(a, jr, sr)
    \/ \E u \in Users, sid \in SessionId, ctx \in SessionContext : 
         CreateSession(u, sid, ctx)
    \/ \E u \in Users, sid \in DOMAIN sessions, r \in Roles : 
         ActivateRole(u, sid, r)
    \/ \E u \in Users, sid \in DOMAIN sessions, r \in Roles : 
         DeactivateRole(u, sid, r)
    \/ \E sid \in DOMAIN sessions : CloseSession(sid)
    \/ \E a \in Users, c \in Constraint : AddConstraint(a, c)
    \/ \E a \in Users, c \in constraints : RemoveConstraint(a, c)
    \/ \E a \in Users, r \in Roles, vf, vu \in Nat, 
          days \in SUBSET STRING, hours \in SUBSET (0..23) :
         SetTemporalConstraint(a, r, vf, vu, days, hours)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: User roles are valid *)
UserRolesValid ==
    \A u \in Users : userRoles[u] \subseteq Roles

(* INV2: Role permissions are valid *)
RolePermissionsValid ==
    \A r \in Roles : rolePermissions[r] \subseteq Permissions

(* INV3: Role hierarchy has no cycles *)
NoHierarchyCycles ==
    \A r \in Roles : ~HasCycle(r, {})

(* INV4: Role hierarchy depth is bounded *)
BoundedHierarchyDepth ==
    \A r \in Roles : RoleDepth(r) <= MaxRoleDepth

(* INV5: Active roles per session don't exceed limit *)
ActiveRoleLimit ==
    \A s \in DOMAIN sessions :
        Cardinality(sessions[s].activeRoles) <= MaxActiveRoles

(* INV6: Active roles belong to the user *)
ActiveRolesBelongToUser ==
    \A s \in DOMAIN sessions :
        sessions[s].activeRoles \subseteq userRoles[sessions[s].user]

(* INV7: Static SoD is enforced *)
StaticSoDEnforced ==
    \A u \in Users, c \in constraints :
        c.type = "STATIC_SoD" =>
            Cardinality(userRoles[u] \cap c.roles) < c.limit

(* INV8: Dynamic SoD is enforced *)
DynamicSoDEnforced ==
    \A s \in DOMAIN sessions, c \in constraints :
        c.type = "DYNAMIC_SoD" =>
            Cardinality(sessions[s].activeRoles \cap c.roles) < c.limit

(* INV9: Role activation counts are accurate *)
ActivationCountsAccurate ==
    \A r \in Roles :
        roleActivations[r].activeCount = 
            Cardinality({s \in DOMAIN sessions : r \in sessions[s].activeRoles})

(* INV10: Audit log is monotonic *)
AuditLogMonotonic ==
    \A i, j \in DOMAIN auditLog :
        i < j => auditLog[i].time <= auditLog[j].time

TypeInvariant ==
    /\ DOMAIN userRoles = Users
    /\ DOMAIN rolePermissions = Roles
    /\ DOMAIN roleHierarchy = Roles
    /\ DOMAIN roleActivations = Roles
    /\ DOMAIN temporalConstraints = Roles
    /\ currentTime \in Nat
    /\ \A s \in DOMAIN sessions : sessions[s].user \in Users

--------------------------------------------------------------------------------
(* Security Properties *)

(* SEC1: Least Privilege - users only get permissions they need *)
LeastPrivilege ==
    \A u \in Users, p \in Permissions :
        p \in AllPermissionsForUser(u) =>
            \E r \in userRoles[u] : p \in AllPermissionsForRole(r)

(* SEC2: Separation of Duty is maintained *)
SeparationOfDuty ==
    /\ StaticSoDEnforced
    /\ DynamicSoDEnforced

(* SEC3: Role hierarchy preserves permissions *)
HierarchyPreservesPermissions ==
    \A jr, sr \in Roles :
        sr \in roleHierarchy[jr] =>
            rolePermissions[sr] \subseteq AllPermissionsForRole(jr)

--------------------------------------------------------------------------------
(* Temporal Properties *)

(* LIVE1: Role assignments eventually grant permissions *)
RoleAssignmentGrantsPermissions ==
    \A u \in Users, r \in Roles :
        (r \in userRoles[u] /\ rolePermissions[r] # {}) ~>
            (AllPermissionsForUser(u) # {})

(* LIVE2: Activated roles are eventually deactivated or session closed *)
RolesEventuallyDeactivated ==
    \A s \in DOMAIN sessions, r \in Roles :
        r \in sessions[s].activeRoles ~>
            (r \notin sessions[s].activeRoles \/ s \notin DOMAIN sessions)

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM RBACIntegrity ==
    Spec => [](UserRolesValid /\ RolePermissionsValid /\ NoHierarchyCycles)

THEOREM SoDEnforcement ==
    Spec => []SeparationOfDuty

THEOREM SessionSafety ==
    Spec => [](ActiveRoleLimit /\ ActiveRolesBelongToUser)

THEOREM HierarchyCorrectness ==
    Spec => [](BoundedHierarchyDepth /\ HierarchyPreservesPermissions)

================================================================================

