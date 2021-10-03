.PHONY: coq
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject  > $@

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

.PHONY: _CoqProject
_CoqProject:
	(echo '-R src ""'; (find src -name *.v | $(SORT_COQPROJECT))) > $@

.PHONY: clean
clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq || true
	rm -f **/*.glob **/*.vo **/*.vok **/*.vos **/.*.aux