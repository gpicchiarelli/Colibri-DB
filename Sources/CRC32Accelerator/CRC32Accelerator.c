#include "CRC32Accelerator.h"
#include <string.h>

#if defined(__ARM_FEATURE_CRC32)
#include <arm_acle.h>
#endif

uint32_t crc32_accelerated(uint32_t seed, const uint8_t *buffer, size_t length, int *used_hw) {
#if defined(__ARM_FEATURE_CRC32)
    uint32_t crc = ~seed;

    const uint8_t *ptr = buffer;
    size_t remaining = length;

    while (remaining >= sizeof(uint64_t)) {
        uint64_t chunk;
        memcpy(&chunk, ptr, sizeof(uint64_t));
        crc = __crc32d(crc, chunk);
        ptr += sizeof(uint64_t);
        remaining -= sizeof(uint64_t);
    }

    if (remaining >= sizeof(uint32_t)) {
        uint32_t chunk;
        memcpy(&chunk, ptr, sizeof(uint32_t));
        crc = __crc32w(crc, chunk);
        ptr += sizeof(uint32_t);
        remaining -= sizeof(uint32_t);
    }

    if (remaining >= sizeof(uint16_t)) {
        uint16_t chunk;
        memcpy(&chunk, ptr, sizeof(uint16_t));
        crc = __crc32h(crc, chunk);
        ptr += sizeof(uint16_t);
        remaining -= sizeof(uint16_t);
    }

    while (remaining > 0) {
        crc = __crc32b(crc, *ptr);
        ptr += 1;
        remaining -= 1;
    }

    if (used_hw) {
        *used_hw = 1;
    }
    return ~crc;
#else
    if (used_hw) {
        *used_hw = 0;
    }
    (void)buffer;
    (void)length;
    return 0;
#endif
}
