invariants: invariants.ml
	ocamlfind ocamlopt -o invariants -linkpkg invariants.ml

test: invariants
	- z3 invariants.smt2
	./invariants > test.smt2
	- z3 test.smt2
	emacs invariants.ml&
	cat RENDU

clean:
	rm -f *~ *.cmi *.cmx *.o invariants
