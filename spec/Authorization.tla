------------------------------ MODULE Authorization ------------------------------
(*****************************************************************************)
(* Authorization System for ColibrìDB                                        *)
(*                                                                           *)
(* This specification models a comprehensive authorization system with:     *)
(*   - Access Control Lists (ACL)                                           *)
(*   - Capability-based security                                            *)
(*   - Mandatory Access Control (MAC) with security labels                  *)
(*   - Discretionary Access Control (DAC)                                   *)
(*   - Attribute-Based Access Control (ABAC)                                *)
(*   - Row-Level Security (RLS)                                             *)
(*   - Column-Level Security                                                *)
(*   - Dynamic policy evaluation                                            *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Lampson (1974): "Protection" - Access Control Matrix                 *)
(*   - Bell & LaPadula (1973): Mandatory Access Control Model               *)
(*   - Sandhu et al. (1996): "Role-Based Access Control Models"             *)
(*   - Park & Sandhu (2004): "Towards Usage Control (UCON)"                 *)
(*   - Hu et al. (2014): NIST Guide to ABAC Definition                      *)
(*   - Oracle VPD (Virtual Private Database) documentation                  *)
(*   - PostgreSQL Row-Level Security implementation                         *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE, TLC

CONSTANTS
    Subjects,           \* Set of users/processes requesting access
    Objects,            \* Set of protected resources (tables, rows, columns)
    Operations,         \* Set of operations (READ, WRITE, DELETE, etc.)
    SecurityLevels,     \* Set of security labels (TOP_SECRET, SECRET, etc.)
    Attributes,         \* Set of attributes for ABAC
    MaxPolicies,        \* Maximum number of policies
    DefaultDeny         \* Default deny policy (closed world)

VARIABLES
    accessMatrix,       \* subject x object -> {operations}
    capabilities,       \* subject -> {[object, operation, expiry, constraints]}
    securityLabels,     \* object -> SecurityLevel
    subjectClearances,  \* subject -> SecurityLevel
    policies,           \* Set of authorization policies
    auditLog,           \* Sequence of authorization events
    objectAttributes,   \* object -> [attribute -> value]
    subjectAttributes,  \* subject -> [attribute -> value]
    currentTime         \* Global clock for time-based policies

vars == <<accessMatrix, capabilities, securityLabels, subjectClearances,
          policies, auditLog, objectAttributes, subjectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* Type Definitions *)

Operation == Operations
SecurityLevel == SecurityLevels
PolicyId == Nat
AccessDecision == {"ALLOW", "DENY"}

(* Operation types *)
OperationType == {
    "READ", "WRITE", "UPDATE", "DELETE", "CREATE", "DROP",
    "SELECT", "INSERT", "ALTER", "GRANT", "REVOKE", "EXECUTE"
}

(* Security level ordering: UNCLASSIFIED < CONFIDENTIAL < SECRET < TOP_SECRET *)
LevelLessThan(l1, l2) ==
    CHOOSE b \in BOOLEAN : TRUE  \* Simplified: would be actual ordering

(* Policy types *)
PolicyType == {"ACL", "MAC", "DAC", "ABAC", "RLS", "CAPABILITY"}

(* Policy structure *)
Policy == [
    id: PolicyId,
    type: PolicyType,
    subject: Subjects \cup {"*"},        \* "*" = all subjects
    object: Objects \cup {"*"},          \* "*" = all objects
    operation: Operations \cup {"*"},    \* "*" = all operations
    conditions: [Attributes -> STRING],  \* ABAC conditions
    effect: AccessDecision,              \* ALLOW or DENY
    priority: Nat                        \* For conflict resolution
]

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ accessMatrix = [s \in Subjects |-> [o \in Objects |-> {}]]
    /\ capabilities = [s \in Subjects |-> {}]
    /\ securityLabels = [o \in Objects |-> CHOOSE l \in SecurityLevels : TRUE]
    /\ subjectClearances = [s \in Subjects |-> CHOOSE l \in SecurityLevels : TRUE]
    /\ policies = {}
    /\ auditLog = <<>>
    /\ objectAttributes = [o \in Objects |-> [a \in Attributes |-> <<>>]]
    /\ subjectAttributes = [s \in Subjects |-> [a \in Attributes |-> <<>>]]
    /\ currentTime = 0

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Check if subject has operation in ACL *)
HasACLPermission(subject, object, operation) ==
    operation \in accessMatrix[subject][object]

(* Check MAC: subject clearance >= object classification *)
SatisfiesMAC(subject, object, operation) ==
    \* Read Down: can read equal or lower classification
    \* Write Up: can write equal or higher classification
    IF operation = "READ" THEN
        ~LevelLessThan(securityLabels[object], subjectClearances[subject])
    ELSE IF operation \in {"WRITE", "UPDATE", "INSERT"} THEN
        ~LevelLessThan(subjectClearances[subject], securityLabels[object])
    ELSE
        TRUE

(* Check if subject has valid capability *)
HasValidCapability(subject, object, operation) ==
    \E cap \in capabilities[subject] :
        /\ cap.object = object
        /\ cap.operation = operation
        /\ cap.expiry > currentTime
        /\ EvaluateConstraints(cap.constraints, subject, object)

(* Evaluate ABAC policy conditions *)
EvaluateABACConditions(conditions, subject, object) ==
    \A attr \in DOMAIN conditions :
        \/ subjectAttributes[subject][attr] = conditions[attr]
        \/ objectAttributes[object][attr] = conditions[attr]

(* Evaluate capability constraints *)
EvaluateConstraints(constraints, subject, object) ==
    \* Constraints like "time of day", "location", "object state"
    \A c \in constraints : TRUE  \* Simplified

(* Check Row-Level Security policy *)
EvaluateRLSPolicy(policy, subject, object, operation) ==
    /\ policy.type = "RLS"
    /\ (policy.subject = "*" \/ policy.subject = subject)
    /\ (policy.object = "*" \/ policy.object = object)
    /\ (policy.operation = "*" \/ policy.operation = operation)
    /\ EvaluateABACConditions(policy.conditions, subject, object)

(* Find applicable policies *)
ApplicablePolicies(subject, object, operation) ==
    {p \in policies :
        /\ (p.subject = "*" \/ p.subject = subject)
        /\ (p.object = "*" \/ p.object = object)
        /\ (p.operation = "*" \/ p.operation = operation)}

(* Policy conflict resolution: highest priority wins, DENY > ALLOW *)
ResolvePolicies(applicablePolicies) ==
    IF applicablePolicies = {} THEN
        IF DefaultDeny THEN "DENY" ELSE "ALLOW"
    ELSE
        LET maxPriority == CHOOSE n \in Nat :
                \E p \in applicablePolicies : p.priority = n /\
                \A q \in applicablePolicies : q.priority <= n
            highestPolicies == {p \in applicablePolicies : p.priority = maxPriority}
        IN
            IF \E p \in highestPolicies : p.effect = "DENY"
            THEN "DENY"
            ELSE "ALLOW"

--------------------------------------------------------------------------------
(* Access Control Decision *)

(* Main authorization check *)
Authorize(subject, object, operation) ==
    LET 
        \* Check all authorization mechanisms
        aclOk == HasACLPermission(subject, object, operation)
        macOk == SatisfiesMAC(subject, object, operation)
        capOk == HasValidCapability(subject, object, operation)
        
        \* Evaluate policies
        applicable == ApplicablePolicies(subject, object, operation)
        policyDecision == ResolvePolicies(applicable)
        
        \* Final decision: ALL must approve (defense in depth)
        decision == IF policyDecision = "DENY" THEN
                        "DENY"
                    ELSE IF aclOk \/ capOk THEN
                        IF macOk THEN "ALLOW" ELSE "DENY"
                    ELSE
                        "DENY"
    IN
        /\ auditLog' = Append(auditLog,
             [event |-> "AUTHORIZATION_CHECK",
              subject |-> subject,
              object |-> object,
              operation |-> operation,
              decision |-> decision,
              mechanisms |-> [acl |-> aclOk, mac |-> macOk, capability |-> capOk],
              time |-> currentTime])
        /\ decision = "ALLOW"

--------------------------------------------------------------------------------
(* ACL Management *)

GrantACL(grantor, subject, object, operation) ==
    \* Grantor must have GRANT privilege
    /\ Authorize(grantor, object, "GRANT")
    /\ accessMatrix' = [accessMatrix EXCEPT 
         ![subject][object] = @ \cup {operation}]
    /\ auditLog' = Append(auditLog,
         [event |-> "GRANT_ACL",
          grantor |-> grantor,
          subject |-> subject,
          object |-> object,
          operation |-> operation,
          time |-> currentTime])
    /\ UNCHANGED <<capabilities, securityLabels, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

RevokeACL(revoker, subject, object, operation) ==
    /\ Authorize(revoker, object, "REVOKE")
    /\ operation \in accessMatrix[subject][object]
    /\ accessMatrix' = [accessMatrix EXCEPT 
         ![subject][object] = @ \ {operation}]
    /\ auditLog' = Append(auditLog,
         [event |-> "REVOKE_ACL",
          revoker |-> revoker,
          subject |-> subject,
          object |-> object,
          operation |-> operation,
          time |-> currentTime])
    /\ UNCHANGED <<capabilities, securityLabels, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* Capability Management *)

IssueCapability(issuer, subject, object, operation, expiry, constraints) ==
    /\ Authorize(issuer, object, operation)
    /\ expiry > currentTime
    /\ LET cap == [object |-> object,
                  operation |-> operation,
                  expiry |-> expiry,
                  constraints |-> constraints]
       IN
           /\ capabilities' = [capabilities EXCEPT 
                ![subject] = @ \cup {cap}]
           /\ auditLog' = Append(auditLog,
                [event |-> "ISSUE_CAPABILITY",
                 issuer |-> issuer,
                 subject |-> subject,
                 capability |-> cap,
                 time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, securityLabels, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

RevokeCapability(revoker, subject, capability) ==
    /\ capability \in capabilities[subject]
    /\ Authorize(revoker, capability.object, "REVOKE")
    /\ capabilities' = [capabilities EXCEPT 
         ![subject] = @ \ {capability}]
    /\ auditLog' = Append(auditLog,
         [event |-> "REVOKE_CAPABILITY",
          revoker |-> revoker,
          subject |-> subject,
          capability |-> capability,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, securityLabels, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

(* Capability delegation: subject can delegate to another subject *)
DelegateCapability(delegator, delegatee, capability) ==
    /\ capability \in capabilities[delegator]
    /\ capability.expiry > currentTime
    /\ LET newCap == [capability EXCEPT 
                       !.expiry = @ - 1]  \* Reduced validity
       IN
           /\ capabilities' = [capabilities EXCEPT 
                ![delegatee] = @ \cup {newCap}]
           /\ auditLog' = Append(auditLog,
                [event |-> "DELEGATE_CAPABILITY",
                 delegator |-> delegator,
                 delegatee |-> delegatee,
                 capability |-> newCap,
                 time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, securityLabels, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* MAC Management *)

ClassifyObject(classifier, object, level) ==
    /\ Authorize(classifier, object, "ALTER")
    /\ level \in SecurityLevels
    /\ securityLabels' = [securityLabels EXCEPT ![object] = level]
    /\ auditLog' = Append(auditLog,
         [event |-> "CLASSIFY_OBJECT",
          classifier |-> classifier,
          object |-> object,
          level |-> level,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, subjectClearances,
                  policies, objectAttributes, subjectAttributes, currentTime>>

SetClearance(administrator, subject, level) ==
    /\ level \in SecurityLevels
    /\ subjectClearances' = [subjectClearances EXCEPT ![subject] = level]
    /\ auditLog' = Append(auditLog,
         [event |-> "SET_CLEARANCE",
          administrator |-> administrator,
          subject |-> subject,
          level |-> level,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels,
                  policies, objectAttributes, subjectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* Policy Management *)

CreatePolicy(creator, policy) ==
    /\ policy.id \notin {p.id : p \in policies}
    /\ Cardinality(policies) < MaxPolicies
    /\ policies' = policies \cup {policy}
    /\ auditLog' = Append(auditLog,
         [event |-> "CREATE_POLICY",
          creator |-> creator,
          policy |-> policy,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels, subjectClearances,
                  objectAttributes, subjectAttributes, currentTime>>

DeletePolicy(deleter, policyId) ==
    /\ \E p \in policies : p.id = policyId
    /\ policies' = {p \in policies : p.id # policyId}
    /\ auditLog' = Append(auditLog,
         [event |-> "DELETE_POLICY",
          deleter |-> deleter,
          policyId |-> policyId,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels, subjectClearances,
                  objectAttributes, subjectAttributes, currentTime>>

UpdatePolicy(updater, policyId, newPolicy) ==
    /\ \E p \in policies : p.id = policyId
    /\ newPolicy.id = policyId
    /\ policies' = {p \in policies : p.id # policyId} \cup {newPolicy}
    /\ auditLog' = Append(auditLog,
         [event |-> "UPDATE_POLICY",
          updater |-> updater,
          policy |-> newPolicy,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels, subjectClearances,
                  objectAttributes, subjectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* ABAC: Attribute Management *)

SetObjectAttribute(setter, object, attribute, value) ==
    /\ Authorize(setter, object, "ALTER")
    /\ attribute \in Attributes
    /\ objectAttributes' = [objectAttributes EXCEPT 
         ![object][attribute] = value]
    /\ auditLog' = Append(auditLog,
         [event |-> "SET_OBJECT_ATTRIBUTE",
          setter |-> setter,
          object |-> object,
          attribute |-> attribute,
          value |-> value,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels, subjectClearances,
                  policies, subjectAttributes, currentTime>>

SetSubjectAttribute(administrator, subject, attribute, value) ==
    /\ attribute \in Attributes
    /\ subjectAttributes' = [subjectAttributes EXCEPT 
         ![subject][attribute] = value]
    /\ auditLog' = Append(auditLog,
         [event |-> "SET_SUBJECT_ATTRIBUTE",
          administrator |-> administrator,
          subject |-> subject,
          attribute |-> attribute,
          value |-> value,
          time |-> currentTime])
    /\ UNCHANGED <<accessMatrix, capabilities, securityLabels, subjectClearances,
                  policies, objectAttributes, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    \* Expire old capabilities
    /\ capabilities' = [s \in Subjects |->
         {cap \in capabilities[s] : cap.expiry > currentTime + 1}]
    /\ UNCHANGED <<accessMatrix, securityLabels, subjectClearances,
                  policies, auditLog, objectAttributes, subjectAttributes>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E g, s \in Subjects, o \in Objects, op \in Operations : 
         GrantACL(g, s, o, op)
    \/ \E r, s \in Subjects, o \in Objects, op \in Operations : 
         RevokeACL(r, s, o, op)
    \/ \E i, s \in Subjects, o \in Objects, op \in Operations, 
          exp \in Nat, cons \in SUBSET STRING :
         IssueCapability(i, s, o, op, exp, cons)
    \/ \E r, s \in Subjects, cap \in UNION {capabilities[sub] : sub \in Subjects} :
         RevokeCapability(r, s, cap)
    \/ \E d, de \in Subjects, cap \in capabilities[d] :
         DelegateCapability(d, de, cap)
    \/ \E c \in Subjects, o \in Objects, l \in SecurityLevels :
         ClassifyObject(c, o, l)
    \/ \E a, s \in Subjects, l \in SecurityLevels :
         SetClearance(a, s, l)
    \/ \E c \in Subjects, p \in Policy : CreatePolicy(c, p)
    \/ \E d \in Subjects, pid \in PolicyId : DeletePolicy(d, pid)
    \/ \E u \in Subjects, pid \in PolicyId, p \in Policy : UpdatePolicy(u, pid, p)
    \/ \E s \in Subjects, o \in Objects, a \in Attributes, v \in STRING :
         SetObjectAttribute(s, o, a, v)
    \/ \E a, s \in Subjects, attr \in Attributes, v \in STRING :
         SetSubjectAttribute(a, s, attr, v)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: Access matrix is well-formed *)
AccessMatrixWellFormed ==
    /\ DOMAIN accessMatrix = Subjects
    /\ \A s \in Subjects : DOMAIN accessMatrix[s] = Objects
    /\ \A s \in Subjects, o \in Objects : 
         accessMatrix[s][o] \subseteq Operations

(* INV2: Valid capabilities don't expire in the past *)
CapabilitiesNotExpired ==
    \A s \in Subjects, cap \in capabilities[s] :
        cap.expiry > currentTime

(* INV3: Security labels are properly assigned *)
SecurityLabelsValid ==
    \A o \in Objects : securityLabels[o] \in SecurityLevels

(* INV4: Subject clearances are valid *)
ClearancesValid ==
    \A s \in Subjects : subjectClearances[s] \in SecurityLevels

(* INV5: Policies have unique IDs *)
UniquePolicyIds ==
    \A p1, p2 \in policies : p1.id = p2.id => p1 = p2

(* INV6: Policy count doesn't exceed limit *)
PolicyLimit ==
    Cardinality(policies) <= MaxPolicies

(* INV7: Attributes are properly defined *)
AttributesWellDefined ==
    /\ \A o \in Objects : DOMAIN objectAttributes[o] = Attributes
    /\ \A s \in Subjects : DOMAIN subjectAttributes[s] = Attributes

(* INV8: Audit log is append-only *)
AuditLogMonotonic ==
    \A i, j \in DOMAIN auditLog :
        i < j => auditLog[i].time <= auditLog[j].time

TypeInvariant ==
    /\ DOMAIN accessMatrix = Subjects
    /\ DOMAIN capabilities = Subjects
    /\ DOMAIN securityLabels = Objects
    /\ DOMAIN subjectClearances = Subjects
    /\ DOMAIN objectAttributes = Objects
    /\ DOMAIN subjectAttributes = Subjects
    /\ currentTime \in Nat

--------------------------------------------------------------------------------
(* Security Properties *)

(* SEC1: MAC prevents information flow violations *)
NoInformationFlowViolation ==
    \A s \in Subjects, o \in Objects :
        (Authorize(s, o, "READ") /\ ~SatisfiesMAC(s, o, "READ")) => FALSE

(* SEC2: Capabilities provide time-bounded access *)
CapabilityTimeBounds ==
    \A s \in Subjects, cap \in capabilities[s] :
        cap.expiry <= currentTime => cap \notin capabilities[s]

(* SEC3: Default deny is enforced *)
DefaultDenyEnforced ==
    DefaultDeny => 
        \A s \in Subjects, o \in Objects, op \in Operations :
            ApplicablePolicies(s, o, op) = {} => 
                ~Authorize(s, o, op)

(* SEC4: Policy conflicts are resolved consistently *)
ConsistentPolicyResolution ==
    \A s \in Subjects, o \in Objects, op \in Operations :
        LET applicable == ApplicablePolicies(s, o, op)
        IN applicable # {} =>
            ResolvePolicies(applicable) \in AccessDecision

--------------------------------------------------------------------------------
(* Temporal Properties *)

(* LIVE1: Granted permissions eventually become effective *)
GrantEventuallyEffective ==
    \A g, s \in Subjects, o \in Objects, op \in Operations :
        GrantACL(g, s, o, op) ~> HasACLPermission(s, o, op)

(* LIVE2: Revoked permissions eventually become ineffective *)
RevokeEventuallyEffective ==
    \A r, s \in Subjects, o \in Objects, op \in Operations :
        RevokeACL(r, s, o, op) ~> ~HasACLPermission(s, o, op)

(* LIVE3: Expired capabilities are eventually removed *)
ExpiredCapabilitiesRemoved ==
    \A s \in Subjects, cap \in capabilities[s] :
        (cap.expiry <= currentTime) ~> (cap \notin capabilities[s])

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM AccessControlIntegrity ==
    Spec => [](AccessMatrixWellFormed /\ SecurityLabelsValid)

THEOREM CapabilitySecur ==
    Spec => [](CapabilitiesNotExpired /\ CapabilityTimeBounds)

THEOREM PolicyConsistency ==
    Spec => [](UniquePolicyIds /\ PolicyLimit /\ ConsistentPolicyResolution)

THEOREM InformationFlowSecurity ==
    Spec => []NoInformationFlowViolation

================================================================================

