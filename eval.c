#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fixed-point.h"

int main(int argc, char *argv[])
{
    if (argc < 2)
        return -1;

    fixedp ipt = {0};
    ipt.data = strtoul(argv[1], NULL, 10);

    if (ipt.data == NAN_INT)
        puts("NAN_INT");
    else if (ipt.data == INF_INT)
        puts("INF_INT");
    else {
        double result = (int) ipt.inte + ((double) ipt.frac / UINT32_MAX);
        printf("%lf\n", result);
    }
    return 0;
}
