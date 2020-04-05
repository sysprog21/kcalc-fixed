#ifndef FIXED_POINT_H

#ifdef __KERNEL__
#include <linux/types.h>
#endif

typedef union __fixedp {
    struct {
        uint32_t frac;
        uint32_t inte;
    };
    uint64_t data;
} fixedp;

#endif /* FIXED_POINT_H */
