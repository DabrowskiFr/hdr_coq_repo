COQC=coqc $(OPT) 
COQDEP=coqdep -R . 
COQFILES=axioms.v tactics.v assoc_list.v eq_syntax.v wf1.v wf2.v wf3.v counting_semantic.v domain_prop.v prog_syntax.v types.v \
         type_safety.v  disjointR.v remove_races.v final.v semantic.v semantic_equiv.v \
         counting_semantic_inv.v counting_semantic_equiv.v counting_points_to.v counting_must_lock.v \
	     sem.v standard_semantic.v points_to_semantic.v sem_equiv.v sem_inv.v points_to.v \
	points_to_race.v must_lock.v escape.v
#	     example.v

all: $(COQFILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(basename $<)	

clean:
	rm -f $(COQFILES:.v=.vo) *~ *.glob
depend : 
	$(COQDEP) $(COQFILES) > .depend 

dot : depend
	dep2dot .depend > dot.dot
	dot2html dot.dot
	dot -Nfontname="/System/Library/Fonts/Times.dfont" -Tpng -o dot.png dot.dot
	cp dot.png datarace/

tar: depend
	rm -fr certified_datarace
	mkdir certified_datarace
	cp $(COQFILES) Makefile .depend certified_datarace/
	tar -czf datarace/certified_datarace.tgz certified_datarace/

coqdoc: depend
	make clean
	make "OPT=-dump-glob dump"
	coqdoc -d datarace/src/ --glob-from dump --no-index -g -html *.v

web:
	cp -r datarace /Volumes/lande/
	cp ../index.html /Volumes/lande/datarace/

-include .depend
