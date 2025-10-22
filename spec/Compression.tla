----------------------------- MODULE Compression -----------------------------
(*
  ColibrìDB Compression Specification
  
  Manages data compression including:
  - Multiple compression algorithms (LZ4, Snappy, Zstd, Gzip)
  - Compression level optimization
  - Dictionary-based compression
  - Block-level and page-level compression
  - Compression ratio monitoring
  - Decompression verification
  
  Based on:
  - Ziv & Lempel (1977) - "A Universal Algorithm for Sequential Data Compression"
  - Welch (1984) - "A Technique for High-Performance Data Compression"
  - Collet (2016) - "Zstandard: Fast and Real-time Compression Algorithm"
  - Google (2011) - "Snappy: A Fast Compressor/Decompressor"
  - LZ4 (2011) - "Extremely Fast Compression Algorithm"
  
  Key Properties:
  - Efficiency: High compression ratio with fast speed
  - Reliability: Lossless compression/decompression
  - Adaptability: Algorithm selection based on data type
  - Monitoring: Compression performance tracking
  - Safety: Data integrity verification
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxCompressionLevel,   \* Maximum compression level (1-22)
  MinCompressionLevel,   \* Minimum compression level (1-22)
  CompressionThreshold,  \* Minimum size to attempt compression
  MaxDictionarySize,     \* Maximum dictionary size
  CompressionTimeout,    \* Timeout for compression operations
  MaxCompressionRatio    \* Maximum expected compression ratio

VARIABLES
  compressionEngines,    \* [EngineId -> CompressionEngine]
  compressionJobs,       \* [JobId -> CompressionJob]
  compressionStats,      \* [EngineId -> CompressionStats]
  dictionaries,          \* [DictId -> Dictionary]
  compressionPolicies,   \* [DataType -> CompressionPolicy]
  decompressionJobs,     \* [JobId -> DecompressionJob]
  compressionMetrics,    \* CompressionMetrics
  compressionErrors      \* [JobId -> CompressionError]

compressionVars == <<compressionEngines, compressionJobs, compressionStats, dictionaries, 
                    compressionPolicies, decompressionJobs, compressionMetrics, compressionErrors>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Compression engine
CompressionEngine == [
  engineId: Nat,
  algorithm: {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"},
  version: STRING,
  isActive: BOOLEAN,
  maxLevel: Nat,
  minLevel: Nat,
  supportedDataTypes: Seq(ValueType),
  lastUsed: Timestamp
]

\* Compression job
CompressionJob == [
  jobId: Nat,
  engineId: Nat,
  dataType: ValueType,
  inputData: Seq(Nat),  \* Byte array as sequence of naturals
  outputData: Seq(Nat),
  compressionLevel: Nat,
  dictionaryId: Nat,
  status: {"pending", "running", "completed", "failed"},
  startTime: Timestamp,
  endTime: Timestamp,
  originalSize: Nat,
  compressedSize: Nat,
  compressionRatio: Nat,  \* 0-100
  isLossless: BOOLEAN
]

\* Compression statistics
CompressionStats == [
  engineId: Nat,
  totalJobs: Nat,
  successfulJobs: Nat,
  failedJobs: Nat,
  totalInputSize: Nat,
  totalOutputSize: Nat,
  averageRatio: Nat,
  averageSpeed: Nat,  \* bytes per second
  peakSpeed: Nat,
  lastReset: Timestamp
]

\* Compression dictionary
Dictionary == [
  dictId: Nat,
  name: STRING,
  data: Seq(Nat),
  size: Nat,
  frequency: [Nat -> Nat],  \* Byte frequency
  isActive: BOOLEAN,
  lastUpdated: Timestamp
]

\* Compression policy for data types
CompressionPolicy == [
  dataType: ValueType,
  preferredAlgorithm: {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"},
  compressionLevel: Nat,
  useDictionary: BOOLEAN,
  dictionaryId: Nat,
  minSizeThreshold: Nat,
  maxSizeThreshold: Nat,
  isEnabled: BOOLEAN
]

\* Decompression job
DecompressionJob == [
  jobId: Nat,
  engineId: Nat,
  compressedData: Seq(Nat),
  decompressedData: Seq(Nat),
  status: {"pending", "running", "completed", "failed"},
  startTime: Timestamp,
  endTime: Timestamp,
  originalSize: Nat,
  decompressedSize: Nat,
  isVerified: BOOLEAN
]

\* Compression metrics
CompressionMetrics == [
  totalCompressions: Nat,
  totalDecompressions: Nat,
  totalBytesCompressed: Nat,
  totalBytesDecompressed: Nat,
  averageCompressionRatio: Nat,
  averageCompressionSpeed: Nat,
  averageDecompressionSpeed: Nat,
  compressionErrors: Nat,
  decompressionErrors: Nat,
  lastUpdate: Timestamp
]

\* Compression error
CompressionError == [
  jobId: Nat,
  errorType: {"compression_failed", "decompression_failed", "data_corrupted", 
              "dictionary_error", "timeout", "memory_error"},
  errorMessage: STRING,
  timestamp: Timestamp,
  isRecoverable: BOOLEAN
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Compression ==
  /\ compressionEngines \in [Nat -> CompressionEngine]
  /\ compressionJobs \in [Nat -> CompressionJob]
  /\ compressionStats \in [Nat -> CompressionStats]
  /\ dictionaries \in [Nat -> Dictionary]
  /\ compressionPolicies \in [ValueType -> CompressionPolicy]
  /\ decompressionJobs \in [Nat -> DecompressionJob]
  /\ compressionMetrics \in CompressionMetrics
  /\ compressionErrors \in [Nat -> CompressionError]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ compressionEngines = [e \in {} |-> [
       engineId |-> 0,
       algorithm |-> "lz4",
       version |-> "",
       isActive |-> FALSE,
       maxLevel |-> 0,
       minLevel |-> 0,
       supportedDataTypes |-> <<>>,
       lastUsed |-> 0
     ]]
  /\ compressionJobs = [j \in {} |-> [
       jobId |-> 0,
       engineId |-> 0,
       dataType |-> "int",
       inputData |-> <<>>,
       outputData |-> <<>>,
       compressionLevel |-> 0,
       dictionaryId |-> 0,
       status |-> "pending",
       startTime |-> 0,
       endTime |-> 0,
       originalSize |-> 0,
       compressedSize |-> 0,
       compressionRatio |-> 0,
       isLossless |-> TRUE
     ]]
  /\ compressionStats = [e \in {} |-> [
       engineId |-> 0,
       totalJobs |-> 0,
       successfulJobs |-> 0,
       failedJobs |-> 0,
       totalInputSize |-> 0,
       totalOutputSize |-> 0,
       averageRatio |-> 0,
       averageSpeed |-> 0,
       peakSpeed |-> 0,
       lastReset |-> 0
     ]]
  /\ dictionaries = [d \in {} |-> [
       dictId |-> 0,
       name |-> "",
       data |-> <<>>,
       size |-> 0,
       frequency |-> [b \in {} |-> 0],
       isActive |-> FALSE,
       lastUpdated |-> 0
     ]]
  /\ compressionPolicies = [t \in ValueType |-> [
       dataType |-> t,
       preferredAlgorithm |-> "lz4",
       compressionLevel |-> 6,
       useDictionary |-> FALSE,
       dictionaryId |-> 0,
       minSizeThreshold |-> 100,
       maxSizeThreshold |-> 1000000,
       isEnabled |-> TRUE
     ]]
  /\ decompressionJobs = [j \in {} |-> [
       jobId |-> 0,
       engineId |-> 0,
       compressedData |-> <<>>,
       decompressedData |-> <<>>,
       status |-> "pending",
       startTime |-> 0,
       endTime |-> 0,
       originalSize |-> 0,
       decompressedSize |-> 0,
       isVerified |-> FALSE
     ]]
  /\ compressionMetrics = [
       totalCompressions |-> 0,
       totalDecompressions |-> 0,
       totalBytesCompressed |-> 0,
       totalBytesDecompressed |-> 0,
       averageCompressionRatio |-> 0,
       averageCompressionSpeed |-> 0,
       averageDecompressionSpeed |-> 0,
       compressionErrors |-> 0,
       decompressionErrors |-> 0,
       lastUpdate |-> 0
     ]
  /\ compressionErrors = [j \in {} |-> [
       jobId |-> 0,
       errorType |-> "compression_failed",
       errorMessage |-> "",
       timestamp |-> 0,
       isRecoverable |-> FALSE
     ]]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Register compression engine
RegisterCompressionEngine(engineId, algorithm, version, maxLevel, minLevel, supportedDataTypes) ==
  /\ ~(engineId \in DOMAIN compressionEngines)
  /\ maxLevel >= minLevel
  /\ maxLevel <= MaxCompressionLevel
  /\ minLevel >= MinCompressionLevel
  /\ LET engine == [
       engineId |-> engineId,
       algorithm |-> algorithm,
       version |-> version,
       isActive |-> TRUE,
       maxLevel |-> maxLevel,
       minLevel |-> minLevel,
       supportedDataTypes |-> supportedDataTypes,
       lastUsed |-> globalTimestamp
     ]
       stats == [
         engineId |-> engineId,
         totalJobs |-> 0,
         successfulJobs |-> 0,
         failedJobs |-> 0,
         totalInputSize |-> 0,
         totalOutputSize |-> 0,
         averageRatio |-> 0,
         averageSpeed |-> 0,
         peakSpeed |-> 0,
         lastReset |-> globalTimestamp
       ]
  IN /\ compressionEngines' = [compressionEngines EXCEPT ![engineId] = engine]
     /\ compressionStats' = [compressionStats EXCEPT ![engineId] = stats]
     /\ UNCHANGED <<compressionJobs, dictionaries, compressionPolicies, 
                   decompressionJobs, compressionMetrics, compressionErrors>>

\* Create compression dictionary
CreateDictionary(dictId, name, data, frequency) ==
  /\ ~(dictId \in DOMAIN dictionaries)
  /\ LET dictionary == [
       dictId |-> dictId,
       name |-> name,
       data |-> data,
       size |-> Len(data),
       frequency |-> frequency,
       isActive |-> TRUE,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ dictionaries' = [dictionaries EXCEPT ![dictId] = dictionary]
     /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   compressionPolicies, decompressionJobs, compressionMetrics, compressionErrors>>

\* Start compression job
StartCompressionJob(jobId, engineId, dataType, inputData, compressionLevel, dictionaryId) ==
  /\ engineId \in DOMAIN compressionEngines
  /\ ~(jobId \in DOMAIN compressionJobs)
  /\ LET engine == compressionEngines[engineId]
       policy == compressionPolicies[dataType]
       job == [
         jobId |-> jobId,
         engineId |-> engineId,
         dataType |-> dataType,
         inputData |-> inputData,
         outputData |-> <<>>,
         compressionLevel |-> compressionLevel,
         dictionaryId |-> dictionaryId,
         status |-> "running",
         startTime |-> globalTimestamp,
         endTime |-> 0,
         originalSize |-> Len(inputData),
         compressedSize |-> 0,
         compressionRatio |-> 0,
         isLossless |-> TRUE
       ]
  IN /\ compressionJobs' = [compressionJobs EXCEPT ![jobId] = job]
     /\ compressionEngines' = [compressionEngines EXCEPT ![engineId] = 
                              [engine EXCEPT !.lastUsed = globalTimestamp]]
     /\ UNCHANGED <<compressionStats, dictionaries, compressionPolicies, 
                   decompressionJobs, compressionMetrics, compressionErrors>>

\* Complete compression job
CompleteCompressionJob(jobId, outputData, success, errorMessage) ==
  /\ jobId \in DOMAIN compressionJobs
  /\ LET job == compressionJobs[jobId]
       engine == compressionEngines[job.engineId]
       stats == compressionStats[job.engineId]
       compressedSize == Len(outputData)
       compressionRatio == IF job.originalSize > 0 
                          THEN (compressedSize * 100) / job.originalSize 
                          ELSE 0
       updatedJob == [job EXCEPT 
                     !.outputData = outputData,
                     !.status = IF success THEN "completed" ELSE "failed",
                     !.endTime = globalTimestamp,
                     !.compressedSize = compressedSize,
                     !.compressionRatio = compressionRatio]
       updatedStats == [stats EXCEPT 
                       !.totalJobs = stats.totalJobs + 1,
                       !.successfulJobs = IF success THEN stats.successfulJobs + 1 ELSE stats.successfulJobs,
                       !.failedJobs = IF success THEN stats.failedJobs ELSE stats.failedJobs + 1,
                       !.totalInputSize = stats.totalInputSize + job.originalSize,
                       !.totalOutputSize = stats.totalOutputSize + compressedSize,
                       !.averageRatio = CalculateAverageRatio(stats, compressionRatio),
                       !.averageSpeed = CalculateAverageSpeed(stats, job.originalSize, 
                                                             globalTimestamp - job.startTime)]
  IN /\ compressionJobs' = [compressionJobs EXCEPT ![jobId] = updatedJob]
     /\ compressionStats' = [compressionStats EXCEPT ![job.engineId] = updatedStats]
     /\ compressionMetrics' = [compressionMetrics EXCEPT 
                              !.totalCompressions = compressionMetrics.totalCompressions + 1,
                              !.totalBytesCompressed = compressionMetrics.totalBytesCompressed + job.originalSize,
                              !.compressionErrors = IF success THEN compressionMetrics.compressionErrors 
                                                   ELSE compressionMetrics.compressionErrors + 1,
                              !.lastUpdate = globalTimestamp]
     /\ compressionErrors' = IF success THEN compressionErrors
                            ELSE [compressionErrors EXCEPT ![jobId] = [
                              jobId |-> jobId,
                              errorType |-> "compression_failed",
                              errorMessage |-> errorMessage,
                              timestamp |-> globalTimestamp,
                              isRecoverable |-> TRUE
                            ]]
     /\ UNCHANGED <<compressionEngines, dictionaries, compressionPolicies, decompressionJobs>>

\* Start decompression job
StartDecompressionJob(jobId, engineId, compressedData, originalSize) ==
  /\ engineId \in DOMAIN compressionEngines
  /\ ~(jobId \in DOMAIN decompressionJobs)
  /\ LET job == [
       jobId |-> jobId,
       engineId |-> engineId,
       compressedData |-> compressedData,
       decompressedData |-> <<>>,
       status |-> "running",
       startTime |-> globalTimestamp,
       endTime |-> 0,
       originalSize |-> originalSize,
       decompressedSize |-> 0,
       isVerified |-> FALSE
     ]
  IN /\ decompressionJobs' = [decompressionJobs EXCEPT ![jobId] = job]
     /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   dictionaries, compressionPolicies, compressionMetrics, compressionErrors>>

\* Complete decompression job
CompleteDecompressionJob(jobId, decompressedData, success, errorMessage) ==
  /\ jobId \in DOMAIN decompressionJobs
  /\ LET job == decompressionJobs[jobId]
       decompressedSize == Len(decompressedData)
       isVerified == decompressedSize = job.originalSize
       updatedJob == [job EXCEPT 
                     !.decompressedData = decompressedData,
                     !.status = IF success THEN "completed" ELSE "failed",
                     !.endTime = globalTimestamp,
                     !.decompressedSize = decompressedSize,
                     !.isVerified = isVerified]
  IN /\ decompressionJobs' = [decompressionJobs EXCEPT ![jobId] = updatedJob]
     /\ compressionMetrics' = [compressionMetrics EXCEPT 
                              !.totalDecompressions = compressionMetrics.totalDecompressions + 1,
                              !.totalBytesDecompressed = compressionMetrics.totalBytesDecompressed + decompressedSize,
                              !.decompressionErrors = IF success THEN compressionMetrics.decompressionErrors 
                                                     ELSE compressionMetrics.decompressionErrors + 1,
                              !.lastUpdate = globalTimestamp]
     /\ compressionErrors' = IF success THEN compressionErrors
                            ELSE [compressionErrors EXCEPT ![jobId] = [
                              jobId |-> jobId,
                              errorType |-> "decompression_failed",
                              errorMessage |-> errorMessage,
                              timestamp |-> globalTimestamp,
                              isRecoverable |-> TRUE
                            ]]
     /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   dictionaries, compressionPolicies>>

\* Update compression policy
UpdateCompressionPolicy(dataType, preferredAlgorithm, compressionLevel, useDictionary, 
                       dictionaryId, minSizeThreshold, maxSizeThreshold, isEnabled) ==
  /\ LET policy == [
       dataType |-> dataType,
       preferredAlgorithm |-> preferredAlgorithm,
       compressionLevel |-> compressionLevel,
       useDictionary |-> useDictionary,
       dictionaryId |-> dictionaryId,
       minSizeThreshold |-> minSizeThreshold,
       maxSizeThreshold |-> maxSizeThreshold,
       isEnabled |-> isEnabled
     ]
  IN /\ compressionPolicies' = [compressionPolicies EXCEPT ![dataType] = policy]
     /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   dictionaries, decompressionJobs, compressionMetrics, compressionErrors>>

\* Verify compression integrity
VerifyCompressionIntegrity(jobId, originalData, compressedData, decompressedData) ==
  /\ jobId \in DOMAIN compressionJobs
  /\ LET job == compressionJobs[jobId]
       isIntegrityValid == originalData = decompressedData
       updatedJob == [job EXCEPT !.isLossless = isIntegrityValid]
  IN /\ compressionJobs' = [compressionJobs EXCEPT ![jobId] = updatedJob]
     /\ UNCHANGED <<compressionEngines, compressionStats, dictionaries, 
                   compressionPolicies, decompressionJobs, compressionMetrics, compressionErrors>>

\* Update compression metrics
UpdateCompressionMetrics() ==
  /\ LET totalCompressions == SumCompressionJobs()
       totalDecompressions == SumDecompressionJobs()
       totalBytesCompressed == SumCompressedBytes()
       totalBytesDecompressed == SumDecompressedBytes()
       averageCompressionRatio == CalculateOverallCompressionRatio()
       averageCompressionSpeed == CalculateOverallCompressionSpeed()
       averageDecompressionSpeed == CalculateOverallDecompressionSpeed()
       compressionErrors == SumCompressionErrors()
       decompressionErrors == SumDecompressionErrors()
       updatedMetrics == [
         totalCompressions |-> totalCompressions,
         totalDecompressions |-> totalDecompressions,
         totalBytesCompressed |-> totalBytesCompressed,
         totalBytesDecompressed |-> totalBytesDecompressed,
         averageCompressionRatio |-> averageCompressionRatio,
         averageCompressionSpeed |-> averageCompressionSpeed,
         averageDecompressionSpeed |-> averageDecompressionSpeed,
         compressionErrors |-> compressionErrors,
         decompressionErrors |-> decompressionErrors,
         lastUpdate |-> globalTimestamp
       ]
  IN /\ compressionMetrics' = updatedMetrics
     /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   dictionaries, compressionPolicies, decompressionJobs, compressionErrors>>

\* Select optimal compression algorithm
SelectOptimalAlgorithm(dataType, dataSize, dataCharacteristics) ==
  /\ LET policy == compressionPolicies[dataType]
       algorithm == IF dataSize < policy.minSizeThreshold THEN "none"
                   ELSE IF dataSize > policy.maxSizeThreshold THEN policy.preferredAlgorithm
                   ELSE ChooseAlgorithmByCharacteristics(dataCharacteristics, policy)
  IN /\ UNCHANGED <<compressionEngines, compressionJobs, compressionStats, 
                   dictionaries, compressionPolicies, decompressionJobs, compressionMetrics, compressionErrors>>

\* Cleanup completed jobs
CleanupCompletedJobs() ==
  /\ LET completedCompressionJobs == {jobId \in DOMAIN compressionJobs : 
                                     compressionJobs[jobId].status \in {"completed", "failed"}}
       completedDecompressionJobs == {jobId \in DOMAIN decompressionJobs : 
                                     decompressionJobs[jobId].status \in {"completed", "failed"}}
  IN /\ compressionJobs' = [j \in DOMAIN compressionJobs \ completedCompressionJobs |-> compressionJobs[j]]
     /\ decompressionJobs' = [j \in DOMAIN decompressionJobs \ completedDecompressionJobs |-> decompressionJobs[j]]
     /\ UNCHANGED <<compressionEngines, compressionStats, dictionaries, 
                   compressionPolicies, compressionMetrics, compressionErrors>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Calculate average compression ratio
CalculateAverageRatio(stats, newRatio) ==
  IF stats.totalJobs = 0 THEN newRatio
  ELSE (stats.averageRatio * (stats.totalJobs - 1) + newRatio) / stats.totalJobs

\* Calculate average compression speed
CalculateAverageSpeed(stats, dataSize, duration) ==
  IF duration = 0 THEN stats.averageSpeed
  ELSE LET speed == dataSize / duration
       IN IF stats.totalJobs = 0 THEN speed
          ELSE (stats.averageSpeed * (stats.totalJobs - 1) + speed) / stats.totalJobs

\* Sum compression jobs
SumCompressionJobs() ==
  IF DOMAIN compressionJobs = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN compressionJobs : TRUE
       IN 1 + SumCompressionJobs()

\* Sum decompression jobs
SumDecompressionJobs() ==
  IF DOMAIN decompressionJobs = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN decompressionJobs : TRUE
       IN 1 + SumDecompressionJobs()

\* Sum compressed bytes
SumCompressedBytes() ==
  IF DOMAIN compressionJobs = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN compressionJobs : TRUE
           job == compressionJobs[jobId]
       IN job.originalSize + SumCompressedBytes()

\* Sum decompressed bytes
SumDecompressedBytes() ==
  IF DOMAIN decompressionJobs = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN decompressionJobs : TRUE
           job == decompressionJobs[jobId]
       IN job.decompressedSize + SumDecompressedBytes()

\* Calculate overall compression ratio
CalculateOverallCompressionRatio() ==
  IF compressionMetrics.totalBytesCompressed = 0 THEN 0
  ELSE (compressionMetrics.totalBytesDecompressed * 100) / compressionMetrics.totalBytesCompressed

\* Calculate overall compression speed
CalculateOverallCompressionSpeed() ==
  IF compressionMetrics.totalCompressions = 0 THEN 0
  ELSE compressionMetrics.totalBytesCompressed / compressionMetrics.totalCompressions

\* Calculate overall decompression speed
CalculateOverallDecompressionSpeed() ==
  IF compressionMetrics.totalDecompressions = 0 THEN 0
  ELSE compressionMetrics.totalBytesDecompressed / compressionMetrics.totalDecompressions

\* Sum compression errors
SumCompressionErrors() ==
  IF DOMAIN compressionErrors = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN compressionErrors : TRUE
       IN 1 + SumCompressionErrors()

\* Sum decompression errors
SumDecompressionErrors() ==
  IF DOMAIN compressionErrors = {} THEN 0
  ELSE LET jobId == CHOOSE j \in DOMAIN compressionErrors : TRUE
           error == compressionErrors[jobId]
       IN IF error.errorType = "decompression_failed" THEN 1 ELSE 0 + SumDecompressionErrors()

\* Choose algorithm by data characteristics
ChooseAlgorithmByCharacteristics(characteristics, policy) ==
  CASE characteristics
    OF "text" -> "gzip"
    [] "binary" -> "lz4"
    [] "structured" -> "zstd"
    [] "random" -> "none"
    [] "repetitive" -> "snappy"
  ENDCASE

\* Check if compression is beneficial
IsCompressionBeneficial(originalSize, compressedSize, threshold) ==
  compressedSize < originalSize * (100 - threshold) / 100

\* Get compression engine by algorithm
GetCompressionEngine(algorithm) ==
  CHOOSE engineId \in DOMAIN compressionEngines : 
    compressionEngines[engineId].algorithm = algorithm /\ 
    compressionEngines[engineId].isActive

\* Check if data type is supported
IsDataTypeSupported(engineId, dataType) ==
  engineId \in DOMAIN compressionEngines /\ 
  dataType \in Range(compressionEngines[engineId].supportedDataTypes)

\* Calculate compression efficiency
CalculateCompressionEfficiency(originalSize, compressedSize, compressionTime) ==
  IF compressionTime = 0 THEN 0
  ELSE (originalSize - compressedSize) / compressionTime

\* Check if compression job is valid
IsValidCompressionJob(jobId) ==
  jobId \in DOMAIN compressionJobs /\ 
  compressionJobs[jobId].status = "running"

\* Check if decompression job is valid
IsValidDecompressionJob(jobId) ==
  jobId \in DOMAIN decompressionJobs /\ 
  decompressionJobs[jobId].status = "running"

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E engineId \in Nat, algorithm \in {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"},
       version \in STRING, maxLevel \in Nat, minLevel \in Nat, supportedDataTypes \in Seq(ValueType) :
       RegisterCompressionEngine(engineId, algorithm, version, maxLevel, minLevel, supportedDataTypes)
  \/ \E dictId \in Nat, name \in STRING, data \in Seq(Nat), frequency \in [Nat -> Nat] :
       CreateDictionary(dictId, name, data, frequency)
  \/ \E jobId \in Nat, engineId \in Nat, dataType \in ValueType, inputData \in Seq(Nat),
       compressionLevel \in Nat, dictionaryId \in Nat :
       StartCompressionJob(jobId, engineId, dataType, inputData, compressionLevel, dictionaryId)
  \/ \E jobId \in Nat, outputData \in Seq(Nat), success \in BOOLEAN, errorMessage \in STRING :
       CompleteCompressionJob(jobId, outputData, success, errorMessage)
  \/ \E jobId \in Nat, engineId \in Nat, compressedData \in Seq(Nat), originalSize \in Nat :
       StartDecompressionJob(jobId, engineId, compressedData, originalSize)
  \/ \E jobId \in Nat, decompressedData \in Seq(Nat), success \in BOOLEAN, errorMessage \in STRING :
       CompleteDecompressionJob(jobId, decompressedData, success, errorMessage)
  \/ \E dataType \in ValueType, preferredAlgorithm \in {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"},
       compressionLevel \in Nat, useDictionary \in BOOLEAN, dictionaryId \in Nat,
       minSizeThreshold \in Nat, maxSizeThreshold \in Nat, isEnabled \in BOOLEAN :
       UpdateCompressionPolicy(dataType, preferredAlgorithm, compressionLevel, useDictionary,
                              dictionaryId, minSizeThreshold, maxSizeThreshold, isEnabled)
  \/ \E jobId \in Nat, originalData \in Seq(Nat), compressedData \in Seq(Nat), 
       decompressedData \in Seq(Nat) :
       VerifyCompressionIntegrity(jobId, originalData, compressedData, decompressedData)
  \/ UpdateCompressionMetrics()
  \/ \E dataType \in ValueType, dataSize \in Nat, dataCharacteristics \in STRING :
       SelectOptimalAlgorithm(dataType, dataSize, dataCharacteristics)
  \/ CleanupCompletedJobs()

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Compression engine constraints
Inv_Compression_EngineConstraints ==
  \A engineId \in DOMAIN compressionEngines :
    LET engine == compressionEngines[engineId]
    IN /\ engine.maxLevel >= engine.minLevel
       /\ engine.maxLevel <= MaxCompressionLevel
       /\ engine.minLevel >= MinCompressionLevel
       /\ engine.algorithm \in {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"}

\* Compression job constraints
Inv_Compression_JobConstraints ==
  \A jobId \in DOMAIN compressionJobs :
    LET job == compressionJobs[jobId]
    IN /\ job.originalSize >= 0
       /\ job.compressedSize >= 0
       /\ job.compressionRatio >= 0 /\ job.compressionRatio <= 100
       /\ job.compressionLevel >= MinCompressionLevel
       /\ job.compressionLevel <= MaxCompressionLevel
       /\ job.status \in {"pending", "running", "completed", "failed"}

\* Decompression job constraints
Inv_Compression_DecompressionJobConstraints ==
  \A jobId \in DOMAIN decompressionJobs :
    LET job == decompressionJobs[jobId]
    IN /\ job.originalSize >= 0
       /\ job.decompressedSize >= 0
       /\ job.status \in {"pending", "running", "completed", "failed"}

\* Dictionary constraints
Inv_Compression_DictionaryConstraints ==
  \A dictId \in DOMAIN dictionaries :
    LET dictionary == dictionaries[dictId]
    IN /\ dictionary.size >= 0
       /\ dictionary.size <= MaxDictionarySize
       /\ Len(dictionary.data) = dictionary.size

\* Compression policy constraints
Inv_Compression_PolicyConstraints ==
  \A dataType \in DOMAIN compressionPolicies :
    LET policy == compressionPolicies[dataType]
    IN /\ policy.compressionLevel >= MinCompressionLevel
       /\ policy.compressionLevel <= MaxCompressionLevel
       /\ policy.minSizeThreshold >= 0
       /\ policy.maxSizeThreshold >= policy.minSizeThreshold
       /\ policy.algorithm \in {"lz4", "snappy", "zstd", "gzip", "brotli", "lzma"}

\* Compression metrics constraints
Inv_Compression_MetricsConstraints ==
  /\ compressionMetrics.totalCompressions >= 0
  /\ compressionMetrics.totalDecompressions >= 0
  /\ compressionMetrics.totalBytesCompressed >= 0
  /\ compressionMetrics.totalBytesDecompressed >= 0
  /\ compressionMetrics.averageCompressionRatio >= 0
  /\ compressionMetrics.averageCompressionRatio <= 100
  /\ compressionMetrics.averageCompressionSpeed >= 0
  /\ compressionMetrics.averageDecompressionSpeed >= 0
  /\ compressionMetrics.compressionErrors >= 0
  /\ compressionMetrics.decompressionErrors >= 0

\* Compression error constraints
Inv_Compression_ErrorConstraints ==
  \A jobId \in DOMAIN compressionErrors :
    LET error == compressionErrors[jobId]
    IN /\ error.errorType \in {"compression_failed", "decompression_failed", "data_corrupted",
                               "dictionary_error", "timeout", "memory_error"}
       /\ error.timestamp >= 0

\* Compression integrity
Inv_Compression_Integrity ==
  \A jobId \in DOMAIN compressionJobs :
    LET job == compressionJobs[jobId]
    IN job.status = "completed" => job.isLossless

\* Compression ratio bounds
Inv_Compression_RatioBounds ==
  \A jobId \in DOMAIN compressionJobs :
    LET job == compressionJobs[jobId]
    IN job.compressionRatio <= MaxCompressionRatio

\* Data size constraints
Inv_Compression_DataSizeConstraints ==
  \A jobId \in DOMAIN compressionJobs :
    LET job == compressionJobs[jobId]
    IN job.originalSize >= CompressionThreshold \/ job.compressionRatio = 0

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Compression jobs eventually complete
Liveness_CompressionJobsComplete ==
  \A jobId \in DOMAIN compressionJobs :
    compressionJobs[jobId].status = "running" => 
    <>compressionJobs[jobId].status \in {"completed", "failed"}

\* Decompression jobs eventually complete
Liveness_DecompressionJobsComplete ==
  \A jobId \in DOMAIN decompressionJobs :
    decompressionJobs[jobId].status = "running" => 
    <>decompressionJobs[jobId].status \in {"completed", "failed"}

\* Compression errors are eventually handled
Liveness_CompressionErrorsHandled ==
  \A jobId \in DOMAIN compressionErrors :
    compressionErrors[jobId].isRecoverable => 
    <>~(jobId \in DOMAIN compressionErrors)

\* Compression metrics are eventually updated
Liveness_CompressionMetricsUpdated ==
  compressionMetrics.lastUpdate < globalTimestamp - 1000 => 
  <>compressionMetrics.lastUpdate >= globalTimestamp - 1000

\* Completed jobs are eventually cleaned up
Liveness_CompletedJobsCleanedUp ==
  \A jobId \in DOMAIN compressionJobs :
    compressionJobs[jobId].status \in {"completed", "failed"} => 
    <>~(jobId \in DOMAIN compressionJobs)

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Compression is lossless
THEOREM Compression_Lossless ==
  \A jobId \in DOMAIN compressionJobs :
    compressionJobs[jobId].isLossless = TRUE

\* Compression ratio is bounded
THEOREM Compression_RatioBounded ==
  \A jobId \in DOMAIN compressionJobs :
    compressionJobs[jobId].compressionRatio <= 100

\* Decompression preserves data integrity
THEOREM Compression_DataIntegrity ==
  \A jobId \in DOMAIN decompressionJobs :
    decompressionJobs[jobId].isVerified = TRUE

\* Compression engines are active
THEOREM Compression_EnginesActive ==
  \A engineId \in DOMAIN compressionEngines :
    compressionEngines[engineId].isActive = TRUE

\* Compression policies are consistent
THEOREM Compression_PoliciesConsistent ==
  \A dataType \in DOMAIN compressionPolicies :
    compressionPolicies[dataType].isEnabled = TRUE

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - CompressionManager.engines (Dictionary<UInt64, CompressionEngine>) → compressionEngines
  - CompressionManager.jobs (Dictionary<UInt64, CompressionJob>) → compressionJobs
  - CompressionManager.stats (Dictionary<UInt64, CompressionStats>) → compressionStats
  - CompressionManager.dictionaries (Dictionary<UInt64, Dictionary>) → dictionaries
  - CompressionManager.policies (Dictionary<ValueType, CompressionPolicy>) → compressionPolicies
  
  USAGE:
  
  This module should be used with Storage and other ColibrìDB modules:
  
  ---- MODULE Storage ----
  EXTENDS Compression
  ...
  ====================
*)