all:
	ott -coq_lngen true -coq_expand_list_types true -i issue4.ott -o issue4.v
	lngen --coq-ott issue4 --coq issue4_inf.v issue4.ott
	coqc issue4.v
	coqc issue4_inf.v
