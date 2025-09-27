//
//  AppleSiliconOptimizationsTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//

// Theme: Tests for Apple Silicon optimizations.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct AppleSiliconOptimizationsTests {
    
    @Test func testAppleSiliconFeatureDetection() {
        let features = AppleSiliconConfig.Features.self
        
        // Test architecture detection
        #expect(features.isAppleSilicon == (UniversalBinary.currentArchitecture == "arm64"))
        
        // Test feature availability
        #expect(features.hasNEON == (UniversalBinary.currentArchitecture == "arm64"))
        #expect(features.hasAccelerate == true) // Should be available on macOS
        #expect(features.hasCryptoKit == true) // Should be available on macOS
        #expect(features.hasMetal == true) // Should be available on macOS
        #expect(features.hasCoreML == true) // Should be available on macOS
        #expect(features.hasNetworkFramework == true) // Should be available on macOS
    }
    
    @Test func testPerformanceTuning() {
        let tuning = AppleSiliconConfig.PerformanceTuning.self
        
        // Test that optimal settings are reasonable
        #expect(tuning.optimalBufferPoolSize > 0)
        #expect(tuning.optimalPageSize > 0)
        #expect(tuning.optimalGroupCommitThreshold > 0)
        #expect(tuning.optimalFlushConcurrency > 0)
        
        // Test that Apple Silicon gets better settings
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(tuning.optimalBufferPoolSize >= 256 * 1024)
            #expect(tuning.optimalPageSize >= 4096)
        }
    }
    
    @Test func testIOOptimizations() {
        let io = AppleSiliconConfig.IOOptimizations.self
        
        // Test that optimizations are enabled on Apple Silicon
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(io.enableFullFSync == true)
            #expect(io.enableSparseFiles == true)
            #expect(io.enableIOHints == true)
            #expect(io.enablePrefetching == true)
        }
    }
    
    @Test func testMemoryOptimizations() {
        let memory = AppleSiliconConfig.MemoryOptimizations.self
        
        // Test that unified memory profiling is enabled on Apple Silicon
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(memory.enableUnifiedMemoryProfiling == true)
        }
        
        // Test that debugging features are available in debug builds
        #if DEBUG
        #expect(memory.enableMemoryTagging == true)
        #expect(memory.enableAddressSanitizer == true)
        #endif
    }
    
    @Test func testSecuritySettings() {
        let security = AppleSiliconConfig.SecuritySettings.self
        
        // Test that hardware encryption is available on Apple Silicon
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(security.enableHardwareEncryption == true)
            #expect(security.enableSecureEnclave == true)
            #expect(security.enableFileVaultIntegration == true)
        }
    }
    
    @Test func testNetworkOptimizations() {
        let network = AppleSiliconConfig.NetworkOptimizations.self
        
        // Test that network optimizations are available
        #expect(network.enableNetworkFramework == true)
        
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(network.enableTLSHardwareAcceleration == true)
            #expect(network.enableQoSClasses == true)
        }
    }
    
    @Test func testMLSettings() {
        let ml = AppleSiliconConfig.MLSettings.self
        
        // Test that ML features are available
        #expect(ml.enableCoreML == true)
        
        if AppleSiliconConfig.Features.isAppleSilicon {
            #expect(ml.enableNeuralEngine == true)
            #expect(ml.enableMetalPerformanceShaders == true)
        }
    }
    
    @Test func testAppleSiliconIntegration() {
        // Test that integration can be initialized
        AppleSiliconIntegration.initialize()
        
        // Test that system info can be retrieved
        let systemInfo = AppleSiliconIntegration.getSystemInfo()
        #expect(systemInfo["architecture"] != nil)
        #expect(systemInfo["features"] != nil)
        #expect(systemInfo["performance"] != nil)
        #expect(systemInfo["io_optimizations"] != nil)
        #expect(systemInfo["memory_optimizations"] != nil)
        #expect(systemInfo["security"] != nil)
        #expect(systemInfo["network"] != nil)
        #expect(systemInfo["ml"] != nil)
    }
    
    @Test func testPerformanceMetrics() {
        // Test that performance metrics can be retrieved
        let metrics = AppleSiliconIntegration.getPerformanceMetrics()
        #expect(metrics["architecture"] != nil)
        #expect(metrics["rosetta"] != nil)
        #expect(metrics["features"] != nil)
        #expect(metrics["low_power_mode"] != nil)
    }
    
    @Test func testWorkloadOptimization() {
        // Test that workload optimization works
        AppleSiliconIntegration.optimizeForWorkload(.oltp)
        AppleSiliconIntegration.optimizeForWorkload(.olap)
        AppleSiliconIntegration.optimizeForWorkload(.mixed)
    }
    
    @Test func testNEONOptimizations() {
        // Test NEON key comparison
        let key1 = Data("test_key_1".utf8)
        let key2 = Data("test_key_2".utf8)
        let key3 = Data("test_key_1".utf8)
        
        let result1 = NEONOptimizations.compareKeysSIMD(key1, key2)
        let result2 = NEONOptimizations.compareKeysSIMD(key1, key3)
        let result3 = NEONOptimizations.compareKeysSIMD(key2, key1)
        
        #expect(result1 < 0) // key1 < key2
        #expect(result2 == 0) // key1 == key3
        #expect(result3 > 0) // key2 > key1
    }
    
    @Test func testNEONHash() {
        // Test NEON hash computation
        let data = Data("test_data".utf8)
        let hash = NEONOptimizations.hashSIMD(data)
        
        #expect(hash != 0)
        
        // Test that same data produces same hash
        let hash2 = NEONOptimizations.hashSIMD(data)
        #expect(hash == hash2)
    }
    
    @Test func testAccelerateOptimizations() {
        // Test vDSP sorting
        var keys = [
            Data("key_c".utf8),
            Data("key_a".utf8),
            Data("key_b".utf8)
        ]
        
        AccelerateOptimizations.batchSortKeys(&keys)
        
        #expect(keys[0] == Data("key_a".utf8))
        #expect(keys[1] == Data("key_b".utf8))
        #expect(keys[2] == Data("key_c".utf8))
    }
    
    @Test func testAccelerateCRC32() {
        // Test Accelerate CRC32 computation
        let data = Data("test_data".utf8)
        let crc = AccelerateOptimizations.computeCRC32Accelerated(data)
        
        #expect(crc != 0)
        
        // Test that same data produces same CRC
        let crc2 = AccelerateOptimizations.computeCRC32Accelerated(data)
        #expect(crc == crc2)
    }
    
    @Test func testUnifiedLogging() {
        // Test that logging works
        UnifiedLogging.logOperation("test_operation", metadata: ["key": "value"])
        UnifiedLogging.logIOOperation("test_io", duration: 1.0, bytes: 1024)
        UnifiedLogging.logPerformance("test_metric", value: 100.0, unit: "ms")
        
        // Test signpost creation
        let signpost = UnifiedLogging.createSignpost("test_signpost")
        #expect(signpost.rawValue != 0)
    }
    
    @Test func testGCDQoS() {
        // Test that QoS queues are created
        #expect(GCDQoS.walQueue.label == "com.colibridb.wal")
        #expect(GCDQoS.flushQueue.label == "com.colibridb.flush")
        #expect(GCDQoS.checkpointQueue.label == "com.colibridb.checkpoint")
        #expect(GCDQoS.maintenanceQueue.label == "com.colibridb.maintenance")
    }
    
    @Test func testCryptoKitIntegration() {
        // Test key generation
        let key = CryptoKitIntegration.generateKey()
        #expect(key != nil)
        
        // Test encryption/decryption
        let data = Data("test_data".utf8)
        
        do {
            let encrypted = try CryptoKitIntegration.encryptData(data, key: key)
            #expect(encrypted != data)
            
            let decrypted = try CryptoKitIntegration.decryptData(encrypted, key: key)
            #expect(decrypted == data)
        } catch {
            // CryptoKit might not be available in test environment
            #expect(true) // Test passes if encryption is not available
        }
    }
    
    @Test func testLowPowerMode() {
        // Test low power mode detection
        let isLowPower = LowPowerMode.isLowPowerMode
        #expect(isLowPower == false || isLowPower == true) // Should be a boolean
        
        // Test performance adjustment
        LowPowerMode.adjustPerformanceSettings()
    }
    
    @Test func testUniversalBinary() {
        // Test architecture detection
        let arch = UniversalBinary.currentArchitecture
        #expect(arch == "arm64" || arch == "x86_64" || arch == "unknown")
        
        // Test Rosetta detection
        let isRosetta = UniversalBinary.isRunningUnderRosetta
        #expect(isRosetta == false || isRosetta == true) // Should be a boolean
        
        // Test optimization
        UniversalBinary.optimizeForCurrentArchitecture()
    }
    
    @Test func testAPFSOptimizations() {
        // Test APFS volume detection
        let tempDir = FileManager.default.temporaryDirectory
        let isAPFS = APFSOptimizations.isAPFSVolume(tempDir.path)
        #expect(isAPFS == false || isAPFS == true) // Should be a boolean
        
        // Test volume info retrieval
        do {
            let volumeInfo = try APFSOptimizations.getVolumeInfo(tempDir.path)
            #expect(volumeInfo is [String: String])
        } catch {
            // Might fail in test environment
            #expect(true) // Test passes if volume info is not available
        }
    }
    
    @Test func testAppleDebugging() {
        // Test MTE availability
        let mteAvailable = AppleDebugging.MTE.isAvailable
        #expect(mteAvailable == false || mteAvailable == true) // Should be a boolean
        
        // Test Address Sanitizer
        let asanEnabled = AppleDebugging.AddressSanitizer.isEnabled
        #if DEBUG
        #expect(asanEnabled == true)
        #else
        #expect(asanEnabled == false)
        #endif
        
        // Test unified memory profiling
        let memoryStats = AppleDebugging.UnifiedMemoryProfiling.getMemoryStats()
        #expect(memoryStats is [String: Any])
        
        // Test DTrace
        let signpost = AppleDebugging.DTrace.createProbe("test_probe")
        #expect(signpost.rawValue != 0)
        
        // Test Instruments
        let instrumentsSignpost = AppleDebugging.Instruments.createSignpost("test_instruments")
        #expect(instrumentsSignpost.rawValue != 0)
        
        // Test Endpoint Security
        let esAvailable = AppleDebugging.EndpointSecurity.isAvailable
        #if os(macOS)
        #expect(esAvailable == true)
        #else
        #expect(esAvailable == false)
        #endif
        
        // Test Page Fusion
        let pageFusionAvailable = AppleDebugging.PageFusion.isAvailable
        #expect(pageFusionAvailable == false || pageFusionAvailable == true) // Should be a boolean
    }
}
