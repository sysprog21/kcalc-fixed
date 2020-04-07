KDIR=/lib/modules/$(shell uname -r)/build

obj-m += calc.o
obj-m += livepatch-calc.o
calc-objs += main.o expression.o
ccflags-y := -std=gnu99 -Wno-declaration-after-statement

GIT_HOOKS := .git/hooks/applied

all: $(GIT_HOOKS)
	make -C $(KDIR) M=$(PWD) modules

$(GIT_HOOKS):
	@scripts/install-git-hooks
	@echo

load: calc.ko
	sudo insmod calc.ko
	sudo chmod 0666 /dev/calc

unload:
	sudo rmmod calc

patch:
	sudo insmod livepatch-calc.ko

unpatch:
	sudo sh -c "echo 0 > /sys/kernel/livepatch/livepatch_calc/enabled"
	sudo rmmod livepatch-calc

check: all eval
	scripts/test.sh

eval: eval.c
	gcc -o scripts/eval eval.c $(ccflags)

clean:
	make -C $(KDIR) M=$(PWD) clean
