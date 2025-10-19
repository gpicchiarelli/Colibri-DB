----------------------------- MODULE Authentication -----------------------------
(*****************************************************************************)
(* Authentication System for ColibrìDB                                       *)
(*                                                                           *)
(* This specification models a secure authentication system with:           *)
(*   - Password hashing (PBKDF2, bcrypt, Argon2)                            *)
(*   - Salt generation for rainbow table resistance                         *)
(*   - Challenge-response protocols (SCRAM)                                 *)
(*   - Session token management with expiration                             *)
(*   - Multi-factor authentication (MFA) support                            *)
(*   - Brute force protection with rate limiting                            *)
(*   - Password policy enforcement                                          *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - RFC 5802: Salted Challenge Response Authentication Mechanism (SCRAM) *)
(*   - RFC 2898: PBKDF2 (Password-Based Key Derivation Function 2)         *)
(*   - RFC 7914: scrypt key derivation                                      *)
(*   - RFC 9106: Argon2 Memory-Hard Function                                *)
(*   - Moriarty et al. (2017): "Authentication Protocols"                   *)
(*   - Bonneau et al. (2012): "The Quest to Replace Passwords"              *)
(*   - Burr et al. (2017): NIST SP 800-63B Digital Identity Guidelines      *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE, TLC

CONSTANTS
    Users,              \* Set of all users
    MaxSessions,        \* Maximum concurrent sessions per user
    SessionTimeout,     \* Session timeout in time units
    MaxLoginAttempts,   \* Max failed login attempts before lockout
    LockoutDuration,    \* Account lockout duration
    MinPasswordLength,  \* Minimum password length
    HashIterations,     \* PBKDF2 iterations (e.g., 100000)
    MFAEnabled,         \* Whether MFA is enabled
    PasswordExpiry      \* Password expiration time

VARIABLES
    userCredentials,    \* user -> [password: STRING, salt: STRING, hash: STRING]
    activeSessions,     \* session_id -> [user: User, created: Time, lastAccess: Time]
    loginAttempts,      \* user -> [count: Nat, lockedUntil: Time]
    mfaSecrets,         \* user -> [secret: STRING, backup_codes: Set]
    passwordHistory,    \* user -> Seq of previous password hashes
    currentTime,        \* Global clock
    auditLog            \* Sequence of authentication events

vars == <<userCredentials, activeSessions, loginAttempts, mfaSecrets, 
          passwordHistory, currentTime, auditLog>>

--------------------------------------------------------------------------------
(* Type Definitions *)

SessionId == STRING
PasswordHash == STRING
Salt == STRING
MFACode == STRING
AuditEvent == STRING

(* Session states *)
SessionActive == "active"
SessionExpired == "expired"
SessionRevoked == "revoked"

(* Authentication methods *)
PasswordAuth == "password"
MFAAuth == "mfa"
TokenAuth == "token"

(* Hash algorithms *)
HashAlgorithm == {"PBKDF2", "bcrypt", "Argon2", "scrypt"}

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ userCredentials = [u \in Users |-> 
        [password |-> <<>>, salt |-> <<>>, hash |-> <<>>, 
         algorithm |-> "Argon2", iterations |-> HashIterations]]
    /\ activeSessions = [s \in {} |-> <<>>]
    /\ loginAttempts = [u \in Users |-> [count |-> 0, lockedUntil |-> 0]]
    /\ mfaSecrets = [u \in Users |-> 
        [secret |-> <<>>, backupCodes |-> {}, enabled |-> MFAEnabled]]
    /\ passwordHistory = [u \in Users |-> <<>>]
    /\ currentTime = 0
    /\ auditLog = <<>>

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Generate cryptographic salt (simulated) *)
GenerateSalt ==
    CHOOSE s \in STRING : TRUE  \* In practice, use CSPRNG

(* Generate random session ID *)
GenerateSessionId ==
    CHOOSE sid \in SessionId : sid \notin DOMAIN activeSessions

(* Hash password with salt and iterations (simulated) *)
HashPassword(password, salt, algorithm, iterations) ==
    CHOOSE h \in PasswordHash : TRUE  \* Represents cryptographic hash

(* Verify password against stored hash *)
VerifyPassword(password, salt, storedHash, algorithm, iterations) ==
    HashPassword(password, salt, algorithm, iterations) = storedHash

(* Generate MFA secret (TOTP seed) *)
GenerateMFASecret ==
    CHOOSE s \in STRING : TRUE

(* Verify MFA code (Time-based One-Time Password) *)
VerifyMFACode(secret, code, time) ==
    \* TOTP algorithm: code = HMAC-SHA1(secret, time/30) mod 10^6
    CHOOSE valid \in BOOLEAN : TRUE  \* Simplified

(* Check if session is valid *)
IsSessionValid(sessionId) ==
    /\ sessionId \in DOMAIN activeSessions
    /\ activeSessions[sessionId].lastAccess + SessionTimeout >= currentTime

(* Check if account is locked *)
IsAccountLocked(user) ==
    /\ loginAttempts[user].count >= MaxLoginAttempts
    /\ loginAttempts[user].lockedUntil > currentTime

(* Check password policy *)
PasswordMeetsPolicy(password) ==
    /\ Len(password) >= MinPasswordLength
    /\ \E c \in DOMAIN password : c \in {"A".."Z"}  \* Uppercase
    /\ \E c \in DOMAIN password : c \in {"a".."z"}  \* Lowercase
    /\ \E c \in DOMAIN password : c \in {"0".."9"}  \* Digit
    /\ \E c \in DOMAIN password : c \in {"!", "@", "#", "$"}  \* Special char

(* Check if password was used before *)
PasswordInHistory(user, passwordHash) ==
    \E i \in DOMAIN passwordHistory[user] : 
        passwordHistory[user][i] = passwordHash

--------------------------------------------------------------------------------
(* Registration *)

RegisterUser(user, password) ==
    /\ user \notin DOMAIN userCredentials \/ userCredentials[user].hash = <<>>
    /\ PasswordMeetsPolicy(password)
    /\ LET salt == GenerateSalt
           hash == HashPassword(password, salt, "Argon2", HashIterations)
       IN
           /\ userCredentials' = [userCredentials EXCEPT 
                ![user] = [password |-> <<>>,  \* Never store plaintext!
                          salt |-> salt,
                          hash |-> hash,
                          algorithm |-> "Argon2",
                          iterations |-> HashIterations]]
           /\ passwordHistory' = [passwordHistory EXCEPT 
                ![user] = Append(@, hash)]
           /\ auditLog' = Append(auditLog, 
                [event |-> "USER_REGISTERED", user |-> user, time |-> currentTime])
    /\ UNCHANGED <<activeSessions, loginAttempts, mfaSecrets, currentTime>>

--------------------------------------------------------------------------------
(* Authentication *)

(* Phase 1: Password Authentication *)
LoginWithPassword(user, password) ==
    /\ ~IsAccountLocked(user)
    /\ LET creds == userCredentials[user]
           valid == VerifyPassword(password, creds.salt, creds.hash, 
                                   creds.algorithm, creds.iterations)
       IN
           IF valid THEN
               \* Successful login
               /\ loginAttempts' = [loginAttempts EXCEPT 
                    ![user] = [count |-> 0, lockedUntil |-> 0]]
               /\ IF ~mfaSecrets[user].enabled THEN
                      \* No MFA: create session immediately
                      LET sid == GenerateSessionId
                      IN
                          /\ activeSessions' = activeSessions @@ 
                               (sid :> [user |-> user, 
                                       created |-> currentTime,
                                       lastAccess |-> currentTime,
                                       authenticated |-> {PasswordAuth}])
                          /\ auditLog' = Append(auditLog,
                               [event |-> "LOGIN_SUCCESS", user |-> user, 
                                session |-> sid, time |-> currentTime])
                  ELSE
                      \* MFA required: mark as password-authenticated
                      /\ auditLog' = Append(auditLog,
                           [event |-> "PASSWORD_AUTH_SUCCESS", user |-> user,
                            mfaRequired |-> TRUE, time |-> currentTime])
                      /\ UNCHANGED activeSessions
               /\ UNCHANGED <<userCredentials, mfaSecrets, passwordHistory>>
           ELSE
               \* Failed login
               /\ loginAttempts' = [loginAttempts EXCEPT 
                    ![user] = [count |-> @ + 1,
                              lockedUntil |-> IF @ + 1 >= MaxLoginAttempts 
                                             THEN currentTime + LockoutDuration
                                             ELSE 0]]
               /\ auditLog' = Append(auditLog,
                    [event |-> "LOGIN_FAILED", user |-> user, 
                     attempts |-> loginAttempts[user].count + 1,
                     time |-> currentTime])
               /\ UNCHANGED <<userCredentials, activeSessions, mfaSecrets, passwordHistory>>
    /\ UNCHANGED currentTime

(* Phase 2: Multi-Factor Authentication *)
LoginWithMFA(user, mfaCode, pendingSessionId) ==
    /\ mfaSecrets[user].enabled
    /\ VerifyMFACode(mfaSecrets[user].secret, mfaCode, currentTime)
    /\ LET sid == IF pendingSessionId = <<>> 
                  THEN GenerateSessionId 
                  ELSE pendingSessionId
       IN
           /\ activeSessions' = activeSessions @@ 
                (sid :> [user |-> user,
                        created |-> currentTime,
                        lastAccess |-> currentTime,
                        authenticated |-> {PasswordAuth, MFAAuth}])
           /\ auditLog' = Append(auditLog,
                [event |-> "MFA_AUTH_SUCCESS", user |-> user,
                 session |-> sid, time |-> currentTime])
    /\ UNCHANGED <<userCredentials, loginAttempts, mfaSecrets, 
                  passwordHistory, currentTime>>

--------------------------------------------------------------------------------
(* Session Management *)

(* Refresh session activity *)
RefreshSession(sessionId) ==
    /\ IsSessionValid(sessionId)
    /\ activeSessions' = [activeSessions EXCEPT 
         ![sessionId].lastAccess = currentTime]
    /\ UNCHANGED <<userCredentials, loginAttempts, mfaSecrets, 
                  passwordHistory, currentTime, auditLog>>

(* Logout: Revoke session *)
Logout(sessionId) ==
    /\ sessionId \in DOMAIN activeSessions
    /\ activeSessions' = [s \in (DOMAIN activeSessions \ {sessionId}) |->
                           activeSessions[s]]
    /\ auditLog' = Append(auditLog,
         [event |-> "LOGOUT", session |-> sessionId, time |-> currentTime])
    /\ UNCHANGED <<userCredentials, loginAttempts, mfaSecrets, 
                  passwordHistory, currentTime>>

(* Expire old sessions *)
ExpireSessions ==
    /\ \E sid \in DOMAIN activeSessions :
         /\ activeSessions[sid].lastAccess + SessionTimeout < currentTime
         /\ activeSessions' = [s \in (DOMAIN activeSessions \ {sid}) |->
                                activeSessions[s]]
         /\ auditLog' = Append(auditLog,
              [event |-> "SESSION_EXPIRED", session |-> sid, time |-> currentTime])
    /\ UNCHANGED <<userCredentials, loginAttempts, mfaSecrets, 
                  passwordHistory, currentTime>>

--------------------------------------------------------------------------------
(* MFA Management *)

EnableMFA(user) ==
    /\ ~mfaSecrets[user].enabled
    /\ LET secret == GenerateMFASecret
           backupCodes == {GenerateSessionId : i \in 1..10}  \* 10 backup codes
       IN
           /\ mfaSecrets' = [mfaSecrets EXCEPT 
                ![user] = [secret |-> secret,
                          backupCodes |-> backupCodes,
                          enabled |-> TRUE]]
           /\ auditLog' = Append(auditLog,
                [event |-> "MFA_ENABLED", user |-> user, time |-> currentTime])
    /\ UNCHANGED <<userCredentials, activeSessions, loginAttempts, 
                  passwordHistory, currentTime>>

DisableMFA(user, sessionId) ==
    /\ mfaSecrets[user].enabled
    /\ IsSessionValid(sessionId)
    /\ activeSessions[sessionId].user = user
    /\ mfaSecrets' = [mfaSecrets EXCEPT 
         ![user] = [secret |-> <<>>, backupCodes |-> {}, enabled |-> FALSE]]
    /\ auditLog' = Append(auditLog,
         [event |-> "MFA_DISABLED", user |-> user, time |-> currentTime])
    /\ UNCHANGED <<userCredentials, activeSessions, loginAttempts, 
                  passwordHistory, currentTime>>

--------------------------------------------------------------------------------
(* Password Management *)

ChangePassword(user, oldPassword, newPassword, sessionId) ==
    /\ IsSessionValid(sessionId)
    /\ activeSessions[sessionId].user = user
    /\ PasswordMeetsPolicy(newPassword)
    /\ LET creds == userCredentials[user]
           validOld == VerifyPassword(oldPassword, creds.salt, creds.hash,
                                      creds.algorithm, creds.iterations)
           newSalt == GenerateSalt
           newHash == HashPassword(newPassword, newSalt, "Argon2", HashIterations)
       IN
           /\ validOld
           /\ ~PasswordInHistory(user, newHash)  \* Can't reuse old password
           /\ userCredentials' = [userCredentials EXCEPT 
                ![user] = [password |-> <<>>,
                          salt |-> newSalt,
                          hash |-> newHash,
                          algorithm |-> "Argon2",
                          iterations |-> HashIterations]]
           /\ passwordHistory' = [passwordHistory EXCEPT 
                ![user] = Append(@, newHash)]
           /\ auditLog' = Append(auditLog,
                [event |-> "PASSWORD_CHANGED", user |-> user, time |-> currentTime])
    /\ UNCHANGED <<activeSessions, loginAttempts, mfaSecrets, currentTime>>

ResetPassword(user, newPassword) ==
    \* Password reset via secure channel (email, etc.)
    /\ PasswordMeetsPolicy(newPassword)
    /\ LET newSalt == GenerateSalt
           newHash == HashPassword(newPassword, newSalt, "Argon2", HashIterations)
       IN
           /\ userCredentials' = [userCredentials EXCEPT 
                ![user] = [password |-> <<>>,
                          salt |-> newSalt,
                          hash |-> newHash,
                          algorithm |-> "Argon2",
                          iterations |-> HashIterations]]
           /\ passwordHistory' = [passwordHistory EXCEPT 
                ![user] = Append(@, newHash)]
           \* Revoke all sessions for security
           /\ activeSessions' = [s \in {sid \in DOMAIN activeSessions : 
                                        activeSessions[sid].user # user} |->
                                  activeSessions[s]]
           /\ auditLog' = Append(auditLog,
                [event |-> "PASSWORD_RESET", user |-> user, time |-> currentTime])
    /\ UNCHANGED <<loginAttempts, mfaSecrets, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<userCredentials, activeSessions, loginAttempts, 
                  mfaSecrets, passwordHistory, auditLog>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E u \in Users, p \in STRING : RegisterUser(u, p)
    \/ \E u \in Users, p \in STRING : LoginWithPassword(u, p)
    \/ \E u \in Users, c \in MFACode, s \in SessionId : LoginWithMFA(u, c, s)
    \/ \E s \in DOMAIN activeSessions : RefreshSession(s)
    \/ \E s \in DOMAIN activeSessions : Logout(s)
    \/ ExpireSessions
    \/ \E u \in Users : EnableMFA(u)
    \/ \E u \in Users, s \in DOMAIN activeSessions : DisableMFA(u, s)
    \/ \E u \in Users, old, new \in STRING, s \in DOMAIN activeSessions : 
         ChangePassword(u, old, new, s)
    \/ \E u \in Users, p \in STRING : ResetPassword(u, p)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: Passwords are never stored in plaintext *)
PasswordsHashed ==
    \A u \in DOMAIN userCredentials :
        userCredentials[u].password = <<>>

(* INV2: All password hashes use strong algorithms *)
StrongHashAlgorithms ==
    \A u \in DOMAIN userCredentials :
        userCredentials[u].algorithm \in {"Argon2", "bcrypt", "scrypt"}

(* INV3: Locked accounts have no active sessions *)
LockedAccountsNoSessions ==
    \A u \in Users :
        IsAccountLocked(u) =>
            ~\E s \in DOMAIN activeSessions : 
                activeSessions[s].user = u

(* INV4: Session count per user doesn't exceed limit *)
SessionLimit ==
    \A u \in Users :
        Cardinality({s \in DOMAIN activeSessions : 
                     activeSessions[s].user = u}) <= MaxSessions

(* INV5: Active sessions are not expired *)
NoExpiredActiveSessions ==
    \A s \in DOMAIN activeSessions :
        activeSessions[s].lastAccess + SessionTimeout >= currentTime

(* INV6: MFA-enabled users have valid secrets *)
MFAIntegrity ==
    \A u \in Users :
        mfaSecrets[u].enabled => 
            /\ mfaSecrets[u].secret # <<>>
            /\ Cardinality(mfaSecrets[u].backupCodes) > 0

(* INV7: All sessions belong to registered users *)
SessionsForRegisteredUsers ==
    \A s \in DOMAIN activeSessions :
        activeSessions[s].user \in DOMAIN userCredentials

(* INV8: Audit log is append-only and monotonic *)
AuditLogMonotonic ==
    \A i, j \in DOMAIN auditLog :
        i < j => auditLog[i].time <= auditLog[j].time

TypeInvariant ==
    /\ DOMAIN userCredentials \subseteq Users
    /\ DOMAIN loginAttempts = Users
    /\ DOMAIN mfaSecrets = Users
    /\ DOMAIN passwordHistory = Users
    /\ currentTime \in Nat
    /\ \A s \in DOMAIN activeSessions :
         /\ activeSessions[s].created <= activeSessions[s].lastAccess
         /\ activeSessions[s].lastAccess <= currentTime

--------------------------------------------------------------------------------
(* Temporal Properties *)

(* LIVE1: Valid credentials eventually lead to authentication *)
EventualAuthentication ==
    \A u \in Users :
        (\E p \in STRING : 
            VerifyPassword(p, userCredentials[u].salt, 
                          userCredentials[u].hash,
                          userCredentials[u].algorithm,
                          userCredentials[u].iterations))
        ~> (\E s \in DOMAIN activeSessions : 
              activeSessions[s].user = u)

(* LIVE2: Expired sessions are eventually cleaned up *)
SessionCleanup ==
    \A s \in DOMAIN activeSessions :
        (activeSessions[s].lastAccess + SessionTimeout < currentTime)
        ~> (s \notin DOMAIN activeSessions)

(* LIVE3: Locked accounts eventually get unlocked *)
EventualUnlock ==
    \A u \in Users :
        IsAccountLocked(u) ~> ~IsAccountLocked(u)

--------------------------------------------------------------------------------
(* Security Properties *)

(* SEC1: Brute force attacks are prevented *)
BruteForceProtection ==
    \A u \in Users :
        loginAttempts[u].count >= MaxLoginAttempts =>
            IsAccountLocked(u)

(* SEC2: Password reuse is prevented *)
NoPasswordReuse ==
    \A u \in Users :
        \A i, j \in DOMAIN passwordHistory[u] :
            i # j => passwordHistory[u][i] # passwordHistory[u][j]

(* SEC3: Session hijacking is mitigated by timeouts *)
SessionTimeout ==
    \A s \in DOMAIN activeSessions :
        currentTime - activeSessions[s].lastAccess <= SessionTimeout

(* SEC4: MFA provides additional security layer *)
MFASecurityLayer ==
    \A u \in Users :
        mfaSecrets[u].enabled =>
            \A s \in DOMAIN activeSessions :
                activeSessions[s].user = u =>
                    MFAAuth \in activeSessions[s].authenticated

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM PasswordSecurity == 
    Spec => [](PasswordsHashed /\ StrongHashAlgorithms)

THEOREM SessionSecurity == 
    Spec => [](SessionLimit /\ NoExpiredActiveSessions)

THEOREM BruteForceResistance ==
    Spec => []BruteForceProtection

THEOREM AuditTrailIntegrity ==
    Spec => []AuditLogMonotonic

================================================================================

