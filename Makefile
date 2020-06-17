compile:
	isabelle build -D . -j 4


quick:
	isabelle build -D . -v -o quick_and_dirty -o skip_proofs
# or:
# isabelle build -D . -j 4 -o quick_and_dirty
