#ifndef CRC32_ACCELERATOR_H
#define CRC32_ACCELERATOR_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/// Computes CRC32 using ARM hardware intrinsics when available.
/// - Parameters:
///   - seed: Initial CRC seed (typically 0xFFFFFFFF).
///   - buffer: Pointer to bytes.
///   - length: Number of bytes.
///   - used_hw: Optional flag set to 1 when hardware path was taken, 0 otherwise.
/// - Returns: Final CRC value when hardware path is available; undefined when not.
uint32_t crc32_accelerated(uint32_t seed, const uint8_t *buffer, size_t length, int *used_hw);

#ifdef __cplusplus
}
#endif

#endif /* CRC32_ACCELERATOR_H */
