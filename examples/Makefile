## This makefile re-runs lngen on all example .ott files and then recompiles them with Coq.

EXAMPLES=Lambda SimpleTypes LF_hhp93 Fsub

all:
	@for i in $(EXAMPLES); do (cd $$i; echo "********* TESTING: $$i *************"; make clean; make rebuild; make); done
