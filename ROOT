session "TAO" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/HOL/Eisbach/Eisbach_Tools"
  theories
	TAO_1_Embedding
	TAO_2_BasicDefinitions
	TAO_3_Semantics
	TAO_4_MetaSolver
	TAO_5_Quantifiable
	TAO_6_Identifiable
	TAO_7_Axioms
	TAO_8_Definitions
	TAO_9_PLM
	TAO_10_PossibleWorlds
	TAO_99_Sanity_Tests
  document_files
    "root.tex"

session "Results" = "TAO" +
  options [document = pdf, document_output = "results", show_question_marks = false, names_short = true]
  theories
	Results
  document_files (in results)
    "root.tex"
	"root.bib"
	"external.aux"

session "Differences" = "TAO" +
  options [document = pdf, document_output = "differences", show_question_marks = false, names_short = true]
  theories
	Differences
  document_files (in differences)
    "root.tex"
	"root.bib"
	"external.aux"
