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
	TAO_98_ArtificialTheorems
	TAO_99_SanityTests
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

session "Documentation" = "TAO" +
  options [document = pdf, document_output = "documentation", show_question_marks = false, names_short = true]
  theories
	Documentation
  document_files (in documentation)
    "root.tex"
	"root.bib"
	"external.aux"

session "Thesis" = "HOL" +
  options [document = pdf, document_output = "thesis", show_question_marks = false, names_short = true]
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
	TAO_98_ArtificialTheorems
	TAO_99_SanityTests
	Thesis
  document_files (in thesis)
    "root.tex"
	"root.bib"
	"external.aux"
	"BNF.pdf"
	"logo.pdf"
