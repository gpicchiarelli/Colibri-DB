# Swift 6.2.1 Limitation - ChaosEngineering Tests

## Problema

I test `ChaosEngineeringTests` non compilano a causa di una limitazione nota di Swift 6.2.1.

### Errore
Swift 6.2.1 non riconosce `@unchecked Sendable` per i tipi restituiti da metodi di actor, anche se:
- I tipi sono marcati come `@unchecked Sendable`
- Tutte le proprietà dei tipi sono Sendable
- I metodi sono marcati con `@preconcurrency`

### Tipi interessati
- `ExperimentOutcome` - marcato come `@unchecked Sendable`
- `ChaosExperiment` - marcato come `@unchecked Sendable`
- `ChaosStats` - marcato come `@unchecked Sendable`
- `ExperimentType` - enum Sendable

### Tentativi di risoluzione
1. ✅ Aggiunto `@unchecked Sendable` a tutti i tipi necessari
2. ✅ Aggiunto `@preconcurrency` ai metodi che restituiscono questi tipi
3. ✅ Creato helper nei test per accettare i risultati non-Sendable
4. ❌ Tentato `nonisolated(unsafe)` - non funziona perché il metodo accede allo stato dell'actor
5. ❌ Tentato wrapper/completion handler - non risolve il problema

### Soluzione temporanea
I test sono stati preparati con helper appropriati, ma non compilano a causa della limitazione di Swift 6.2.1.

### Soluzione futura
- Aggiornare a una versione più recente di Swift che risolve questo problema
- Oppure cambiare l'API per usare un approccio diverso (es. completion handler, wrapper type)

## Riferimenti
- Swift 6.2.1 strict concurrency checking
- `@unchecked Sendable` limitation for actor return types

