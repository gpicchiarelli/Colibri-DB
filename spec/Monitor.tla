---------------------------- MODULE Monitor ----------------------------
(***************************************************************************
 * TLA+ Specification: System Monitoring and Observability
 *
 * Based on:
 * [1] Lamport, L. (1983).
 *     "What Good is Temporal Logic?"
 *     IFIP Congress, pp. 657-668.
 *     Monitoring temporal properties
 *
 * [2] Barham, P., et al. (2003).
 *     "Magpie: Online Modelling and Performance-aware Systems"
 *     HotOS IX.
 *     Distributed system monitoring
 *
 * [3] Sigelman, B. H., et al. (2010).
 *     "Dapper, a Large-Scale Distributed Systems Tracing Infrastructure"
 *     Google Technical Report.
 *     Distributed tracing
 *
 * Models metrics collection, health checks, alerting, and telemetry.
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    Components,         \* System components to monitor
    MetricTypes,        \* Types of metrics (CPU, memory, latency, etc.)
    Thresholds          \* Alert thresholds

VARIABLES
    metrics,            \* [<<component, metric>> |-> value]
    alerts,             \* Set of active alerts
    healthStatus,       \* [component |-> health]
    telemetry           \* Sequence of telemetry events

vars == <<metrics, alerts, healthStatus, telemetry>>

HealthStates == {"HEALTHY", "DEGRADED", "UNHEALTHY"}

TypeOK ==
    /\ metrics \in [((Components \X MetricTypes)) -> Nat]
    /\ alerts \subseteq (Components \X MetricTypes)
    /\ healthStatus \in [Components -> HealthStates]
    /\ telemetry \in Seq([component: Components, metric: MetricTypes, 
                          value: Nat, timestamp: Nat])

Init ==
    /\ metrics = [link \in (Components \X MetricTypes) |-> 0]
    /\ alerts = {}
    /\ healthStatus = [c \in Components |-> "HEALTHY"]
    /\ telemetry = <<>>

\* Update metric
UpdateMetric(component, metric, value) ==
    /\ component \in Components
    /\ metric \in MetricTypes
    /\ metrics' = [metrics EXCEPT ![<<component, metric>>] = value]
    /\ telemetry' = Append(telemetry, 
        [component |-> component, metric |-> metric, 
         value |-> value, timestamp |-> Len(telemetry)])
    /\ UNCHANGED <<alerts, healthStatus>>

\* Trigger alert if threshold exceeded
CheckThreshold(component, metric) ==
    /\ component \in Components
    /\ metric \in MetricTypes
    /\ metrics[<<component, metric>>] > Thresholds
    /\ alerts' = alerts \cup {<<component, metric>>}
    /\ healthStatus' = [healthStatus EXCEPT ![component] = "DEGRADED"]
    /\ UNCHANGED <<metrics, telemetry>>

\* Clear alert
ClearAlert(component, metric) ==
    /\ <<component, metric>> \in alerts
    /\ metrics[<<component, metric>>] <= Thresholds
    /\ alerts' = alerts \ {<<component, metric>>}
    /\ healthStatus' = [healthStatus EXCEPT ![component] = 
        IF \E m \in MetricTypes : <<component, m>> \in alerts'
        THEN "DEGRADED"
        ELSE "HEALTHY"]
    /\ UNCHANGED <<metrics, telemetry>>

Next ==
    \/ \E c \in Components, m \in MetricTypes, v \in Nat :
        UpdateMetric(c, m, v)
    \/ \E c \in Components, m \in MetricTypes :
        CheckThreshold(c, m)
    \/ \E c \in Components, m \in MetricTypes :
        ClearAlert(c, m)

Spec == Init /\ [][Next]_vars

\* Alert consistency
AlertConsistency ==
    \A c \in Components, m \in MetricTypes :
        <<c, m>> \in alerts => metrics[<<c, m>>] > Thresholds

THEOREM Spec => []TypeOK
THEOREM Spec => []AlertConsistency

================================================================================

