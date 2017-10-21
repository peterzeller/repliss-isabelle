(*	compile with:
		isabelle build -D .
	or:
		isabelle build -D . -j 4 -o quick_and_dirty
*)
session "repliss" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/HOL/Library/Sublist"
    "~~/src/HOL/Library/LaTeXsugar"
    "~~/src/HOL/Library/OptionalSugar"
    "~~/src/HOL/Library/Multiset"
    "~~/src/HOL/Library/Option_ord"
  theories [show_question_marks = false, names_short]
    invariant_simps
  document_files
    "root.tex"
    "mathpartir.sty"
