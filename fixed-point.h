#ifndef FIXED_POINT_H
#define FIXED_POINT_H

#ifdef __KERNEL__
#include <linux/types.h>
#else
#include <stdint.h>
#endif

const uint64_t INF_INT = 9223372036854775808U;
const uint64_t NAN_INT = 1U;

typedef union __fixedp {
    struct {
        uint32_t frac;
        uint32_t inte;
    };
    uint64_t data;
} fixedp;

#endif /* FIXED_POINT_H */
