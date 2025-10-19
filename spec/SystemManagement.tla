----------------------------- MODULE SystemManagement -----------------------------
(*
  System Management Bridge Module
  
  Integrates system management components:
  - Catalog: System catalog and metadata
  - ConstraintManager: Constraints and triggers
  - Monitor: Performance monitoring
  - MultiDatabaseCatalog: Multi-database management
  - ResourceQuotas: Resource limits per user/database
  - ConnectionPooling: Connection pooling
  - MemoryManagement: Memory allocation and tracking
  - Compression: Data compression
  - APFSOptimizations: macOS APFS optimizations
  
  Provides unified system management interface
  
  Cross-Module Invariants:
  1. Resource Limits: All resource usage within quotas
  2. Catalog Consistency: Catalog matches actual objects
  3. Monitoring Accuracy: Metrics reflect actual state
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS CORE, Catalog, ConstraintManager, Monitor, MultiDatabaseCatalog,
        ResourceQuotas, ConnectionPooling, MemoryManagement, 
        Compression, APFSOptimizations

VARIABLES
  systemConfig,          \* [ConfigKey -> ConfigValue]
  resourceUsage,         \* [Resource -> CurrentUsage]
  performanceMetrics,    \* [Metric -> Value]
  alertState             \* [AlertType -> BOOLEAN]

sysMgmtVars == <<systemConfig, resourceUsage, performanceMetrics, alertState>>

allVars == <<catalogVars, constraintVars, monitorVars, multiDBVars, quotaVars,
             poolVars, memVars, compressionVars, apfsVars, sysMgmtVars>>

TypeOK_SysMgmt ==
  /\ TypeOK_Catalog /\ TypeOK_ConstraintManager /\ TypeOK_Monitor
  /\ TypeOK_MultiDB /\ TypeOK_Quotas /\ TypeOK_ConnectionPool
  /\ TypeOK_MemoryManagement /\ TypeOK_Compression /\ TypeOK_APFS
  /\ systemConfig \in [STRING -> STRING]
  /\ resourceUsage \in [STRING -> Nat]
  /\ performanceMetrics \in [STRING -> Nat]
  /\ alertState \in [STRING -> BOOLEAN]

Init_SysMgmt ==
  /\ Init_Catalog /\ Init_ConstraintManager /\ Init_Monitor
  /\ Init_MultiDB /\ Init_Quotas /\ Init_ConnectionPool
  /\ Init_MemoryManagement /\ Init_Compression /\ Init_APFS
  /\ systemConfig = [key \in {} |-> ""]
  /\ resourceUsage = [res \in {} |-> 0]
  /\ performanceMetrics = [metric \in {} |-> 0]
  /\ alertState = [alert \in {} |-> FALSE]

\* Check resource quota
CheckQuota(userId, resource, amount) ==
  /\ LET currentUsage == resourceUsage[userId \o "_" \o resource]
         quota == GetUserQuota(userId, resource)
     IN currentUsage + amount <= quota

\* Allocate resource
AllocateResource(userId, resource, amount) ==
  /\ CheckQuota(userId, resource, amount)
  /\ resourceUsage' = [resourceUsage EXCEPT 
       ![userId \o "_" \o resource] = @ + amount]
  /\ UNCHANGED <<systemConfig, performanceMetrics, alertState>>

\* Update performance metrics
UpdateMetrics ==
  /\ performanceMetrics' = [
       "queries_per_second" |-> Monitor_GetQPS(),
       "transactions_per_second" |-> Monitor_GetTPS(),
       "active_connections" |-> ConnectionPool_ActiveCount(),
       "memory_usage" |-> MemoryManagement_CurrentUsage(),
       "cache_hit_rate" |-> Monitor_GetCacheHitRate()]
  /\ UNCHANGED <<systemConfig, resourceUsage, alertState>>

\* Check and trigger alerts
CheckAlerts ==
  /\ alertState' = [
       "high_memory" |-> performanceMetrics["memory_usage"] > 80,
       "too_many_connections" |-> performanceMetrics["active_connections"] > 90,
       "low_cache_hit" |-> performanceMetrics["cache_hit_rate"] < 70]
  /\ UNCHANGED <<systemConfig, resourceUsage, performanceMetrics>>

Next_SysMgmt ==
  \/ \E uid \in STRING, res \in STRING, amt \in Nat: AllocateResource(uid, res, amt)
  \/ UpdateMetrics
  \/ CheckAlerts
  \/ Next_Catalog \/ Next_ConstraintManager \/ Next_Monitor
  \/ Next_MultiDB \/ Next_Quotas \/ Next_ConnectionPool
  \/ Next_MemoryManagement \/ Next_Compression \/ Next_APFS

Spec_SysMgmt == Init_SysMgmt /\ [][Next_SysMgmt]_allVars

\* Invariant: Resource limits respected
Inv_SysMgmt_QuotasRespected ==
  \A uid \in STRING, res \in STRING:
    resourceUsage[uid \o "_" \o res] <= GetUserQuota(uid, res)

\* Invariant: Catalog consistency
Inv_SysMgmt_CatalogConsistent ==
  Catalog_AllObjectsValid()

THEOREM SysMgmt_QuotaEnforcement ==
  Spec_SysMgmt => []Inv_SysMgmt_QuotasRespected

=============================================================================

