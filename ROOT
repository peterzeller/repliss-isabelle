(*	compile with:
		isabelle build -D .
	or:
		isabelle build -D . -j 4 -o quick_and_dirty
*)
session "repliss" = "HOL" +
  options [document = pdf, document_output = "output"]
  sessions
    "HOL-Library"
    "HOL-Eisbach"
    "Case_Labeling"
    "fuzzyrule"
    "ZFC_in_HOL"
 (* theories [document = false]
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/HOL/Library/Sublist"
    "~~/src/HOL/Library/LaTeXsugar"
    "~~/src/HOL/Library/OptionalSugar"
    "~~/src/HOL/Library/Multiset"
    "~~/src/HOL/Library/Option_ord" *)
  theories [show_question_marks = false, names_short]
    invariant_simps
    completeness
    crdt_examples
    example_userbase
    example_chat
    example_loop_max
    example_loop_max2
  document_files
    "root.tex"
    "mathpartir.sty"
    build