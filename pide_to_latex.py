#!/usr/bin/env python3
from html.parser import HTMLParser
from pathlib import Path
import sys
import re

keys = {}

referencedEntities = {
	"AOT_model.<o>",
	"AOT_model.w",
	"AOT_model.AOT_model_d<o>",
	"AOT_model.AOT_model_valid_in",
	"AOT_model.AOT_model_proposition_choice",
	"AOT_model.<omega>",
	"AOT_model.<sigma>",
	"AOT_model.null",
	"AOT_model.<upsilon>",
	"AOT_model.urrel",
	"AOT_model.<alpha><sigma>",
	"AOT_model.<alpha><sigma>'",
	"AOT_model.<alpha><sigma>_pigeonhole",
	"AOT_model.<kappa>",
	"AOT_model.AOT_Term",
	"AOT_model.AOT_IndividualTerm",
	"AOT_model.rel",
	"AOT_model.rel_to_urrel",
	"AOT_model.<kappa><upsilon>",
	"AOT_model.AOT_var",
	"AOT_syntax.AOT_denotes",
	"AOT_semantics.AOT_sem_imp",
	"AOT_semantics.AOT_sem_desc_denotes",
	"AOT_semantics.AOT_sem_exe",
	"AOT_semantics.AOT_Enc",
	"AOT_semantics.AOT_UnaryEnc",
	"AOT_semantics.AOT_<kappa>",
	"AOT_semantics.AOT_<kappa>s",
	"AOT_semantics.AOT_instance_of_cqt_2",
	"AOT_semantics.AOT_model_lambda_denotes",
	"AOT_semantics.AOT_instance_of_cqt_2_intros_const",
	"AOT_semantics.AOT_instance_of_cqt_2_intros_exe_const",
	"AOT_semantics.AOT_instance_of_cqt_2_intros_not",
	"AOT_semantics.AOT_instance_of_cqt_2_exe_arg",
	"AOT_semantics.AOT_instance_of_cqt_2_enc_arg",
	"AOT_PLM.AOT_Term_id",
	"AOT_PLM.unvarify",
	"AOT_RestrictedVariables.unconstrain",
	"AOT_NaturalNumbers.pred_coex",
	"AOT_NaturalNumbers.numbers_prop_den",
	"AOT_Axioms.AOT_ExtendedModel.indistinguishable_ord_enc_all",
	"AOT_Axioms.AOT_ExtendedModel.indistinguishable_ord_enc_ex",
	"AOT_ExtendedRelationComprehension.denotes_all",
	"AOT_ExtendedRelationComprehension.denotes_ex",
	"AOT_ExtendedRelationComprehension.denotes_ex_neg",
	"AOT_ExtendedRelationComprehension.Comprehension_1",
	"AOT_ExtendedRelationComprehension.Comprehension_2",
	"AOT_ExtendedRelationComprehension.Comprehension_1'",
	"AOT_ExtendedRelationComprehension.Comprehension_2'",
	"AOT_ExtendedRelationComprehension.Comprehension_3",
	"AOT_misc.PossiblyNumbersEmptyPropertyImpliesZero",
	"AOT_misc.Numbers'DistinctZeroes",
	"AOT_misc.restricted_identity",
	"AOT_misc.induction'",
	"AOT_misc.OrdinaryExtensionOf",
	"AOT_misc.BeingOrdinaryExtensionOfDenotes",
	"AOT_misc.ConceptOfOrdinaryProperty",
	"AOT_misc.concept_inclusion_denotes_1",
	"AOT_misc.concept_inclusion_denotes_2",
	"AOT_misc.FormOfOrdinaryProperty"
}

with open("./keys.list") as f:
	for line in f.readlines():
		split = line.strip().split('|')
		keys[split[1]] = split[0]

linerefs = {}

with open("./AOT.ExportInfo/info2") as f:
	for line in f.readlines():
		split = line.strip().split('|')
		theory = split[0]
		key = split[1]
		line = split[2]
		if not theory in linerefs:
			linerefs[theory] = {}
		linerefs[theory][line] = key

unicode_map = {
	'\u2015': "hyphen",
	'\u00d7': "times",
	'\u27e8': "langle",
	'\u27e9': "rangle",
	'\u00a6': "pipe",

	'\u2190': "leftarrow",
	'\u2192': "rightarrow",
	'\u2193': "down",
	'\u00ac': "neg",
	'\u2039': "cartoucheleft",
	'\u203A': "cartoucheright",
	'\u00AB': "guillemotleft",
	'\u00BB': "guillemotright",
	'\u2026': "ldots",
	'\u0007': "parm",
	'\u0393': "Gamma",
	'\u0394': "Delta",
	'\u0398': "Theta",
	'\u039B': "Lambda",
	'\u039E': "Xi",
	'\u03A0': "Pi",
	'\u03A8': "Psi",
	'\u03B1': "alpha",
	'\u03B2': "beta",
	'\u03B3': "gamma",
	'\u03B4': "delta",
	'\u03B5': "epsilon",
	'\u03B6': "zeta",
	'\u03B7': "eta",
	'\u03B8': "vartheta",
	'\u03B9': "iota",
	'\u03BA': "kappa",
	'\u03BB': "lambda",
	'\u03BC': "mu",
	'\u03BD': "nu",
	'\u03BE': "xi",
	'\u03C3': "sigma",
	'\u03C4': "tau",
	'\u03C7': "chi",
	'\u03C8': "psi",
	'\u03C9': "omega",
	'\u03C5': "upsilon",
	'\u03A3': "Sigma",
	'\u03A6': "Phi",
	'\u2115': "mathbbN",
	'\u211B': "mathcalR",
	'\u21D2': "Rightarrow",
	'\u2200': "forall",
	'\u2203': "exists",
	'\u2204': "notexists",
	'\u2205': "emptyset",
	'\u2208': "in",
	'\u2209': "notin",
	'\u2211': "sum",
	'\u2218': "circ",
	'\u2227': "land",
	'\u2228': "lor",
	'\u2248': "approx",
	'\u2260': "noteq",
	'\u2261': "equiv",
	'\u2264': "leq",
	'\u2265': "geq",
	'\u227c': "preccurlyeq",
	'\u22c3': "bigcup",
	'\u2286': "subseteq",
	'\u222A': "cup",
	'\u22A2': "vdash",
	'\u22A4': "top",
	'\u22A5': "bot",
	'\u22A8': "models",
	'\u22B4': "trianglelefteq",
	'\u22C0': "bigwedge",
	'\u25A1': "Box",
	'\u25C7': "Diamond",
	'\u27F7': "longleftrightarrow",
	'\u27F9': "Longrightarrow",
	'\u2983': "lBrace",
	'\u2984': "rBrace",
	'\u2987': "lParen",
	'\u2988': "rParen",
	'\U0001D49C': "mathcalA",
	'\U0001D4AB': "mathcalP",
	'\U0001D4AE': "mathcalS",
	'\U0001D5C8': "mathrmo",
	'\u27F6': "longrightarrow",
	'\u21D4': "Leftrightarrow",
	'\u03C6': "varphi",
}

labelPattern = re.compile(r'\u2039\\label{([^}]*)}\u203A', re.UNICODE)
lineLabelPattern = re.compile(r'\u2039\\linelabel{([^}]*)}\u203A', re.UNICODE)
specialAntiquotePattern = re.compile(r'\\<\^([^>]*)>')

class ReferenceChecker(HTMLParser):
	def __init__(self, theories):
		HTMLParser.__init__(self)
		self.theories = {}
		for _,thy,_ in theories:
			self.theories[thy] = True
	def handle_starttag(self, tag, attrs):
		endtagfuns = []
		if tag == "entity":
			defline = None
			deffile = None
			for (attr,value) in attrs:
				if attr == "def_line":
					defline = value
				if attr == "def_file":
					deffile = value
			if deffile and defline:
				theory = Path(deffile).stem
				ext = Path(deffile).suffix
				if ext == ".thy" and theory in self.theories:
					if not theory in linerefs:
						linerefs[theory] = {}
					if not defline in linerefs[theory]:
						linerefs[theory][defline] = ""

class PideXMLParser(HTMLParser):
	def __init__(self, thy, chapter, section):
		HTMLParser.__init__(self)
		self.endtagfuns = []
		self.start_of_line = True
		self.line_indent = 0
		self.sub = 0
		self.sup = 0
		self.bold = 0
		self.line = 1
		self.defs = {}
		self.defsByName = {}
		self.current_def = None
		self.is_plain_text = False
		self.is_section = False
		self.theory = thy
		self.section = section
		self.chapter = chapter
		self.linerefs = linerefs[self.theory]

	def handle_starttag(self, tag, attrs):
		endtagfuns = []
		if tag == "entity":
			refname = None
			defname = None
			deffile = None
			defline = None
			name = None
			is_fact = False
			is_command = False
			for (attr,value) in attrs:
				if attr == "def":
					defname = value
				if attr == "def_file":
					deffile = value
				if attr == "def_line":
					defline = value
				if attr == "ref":
					refname = value
				if attr == "name":
					name = value
				if attr == "kind" and value == "fact":
					is_fact = True
				elif attr == "kind" and value == "command":
					is_command = True
			if is_command and name == "subsection":
				print("\\phantomsection", end="")
				self.is_section = True
			if defname and name:
				name = name.replace('\\','').replace('$','')
				if name in referencedEntities:
					print("\\plmlabel[{}.{}.{}]{{AOT:{}}}".format(self.chapter,self.section, self.line, name), end="")
				if name and is_fact:
					name = name.split('.')[-1]
					self.defsByName[name] = defname
					name = name.split('[')[0]
					name = name.split(':')
					if name[0] in keys:
							self.current_def = keys[name[0]]
							for s in name[1:]:
									self.current_def += '.' + s

			if defline and deffile:
				theory = Path(deffile).stem
				ext = Path(deffile).suffix
				if ext == ".thy" and theory in linerefs and defline in linerefs[theory]:
					endtagfuns.append(lambda self: print("}", end=""))
					print("\\hyperlink{{{}.L{}}}{{".format(theory, defline), end="")
		elif tag == "plain_text":
			self.is_plain_text = True
		self.endtagfuns.append(endtagfuns)
		print("\\begin{{{}}}".format("pide"+tag), end="")

	def markLine(self):
		if str(self.line) in self.linerefs:
			label = self.linerefs[str(self.line)]
			print("\\myhypertarget{{{}.L{}}}{{}}".format(self.theory, self.line), end="")
			if len(label) > 0:
				labelKey = label.strip().split(":")[0].split("[")[0]
				if labelKey in keys:
					label = label.replace('\\','').replace('$','')
					print("\\plmlabel[{}.{}.{}]{{AOT:{}}}".format(self.chapter,self.section, self.line, label), end="")

	def handle_endtag(self, tag):
		print("\\end{{{}}}".format("pide"+tag), end="")
		for fun in self.endtagfuns.pop():
			fun(self)

	def handle_data(self, data):
		tokens = []
		data_clean = ""
		specialAntiquote = False
		if m := specialAntiquotePattern.match(data):
			print("\\begin{pidespecialantiquote}", end="")
			data = m.group(1)
			specialAntiquote = True
		if self.is_plain_text and (m := labelPattern.match(data)):
			print("\\plmlabelnosec[{}.{}.{}]{{{}}}".format(self.chapter,self.section, self.line, m.group(1)), end="")
		if self.is_plain_text and (m := lineLabelPattern.match(data)):
			print("\\plmlabel[{}.{}.{}]{{AOT:{}}}".format(self.chapter,self.section, self.line, m.group(1)), end="")
		for c in data:
			if c == "\n":
				if self.start_of_line:
					self.markLine()
				if len(data_clean) > 0:
					tokens.append(data_clean)
					data_clean=""
				if self.current_def:
					tokens.append("\\hspace*{\\fill}")
					tokens.append("{\\scriptsize\\textrm{(" + self.current_def + ")}}")
					self.current_def = None
				tokens.append("\\newline\n")
				self.start_of_line = True
				self.line_indent = 0
				self.line = self.line + 1
			elif c == ' ':
				if len(data_clean) > 0:
					tokens.append(data_clean)
					data_clean=""
				if self.start_of_line:
					self.line_indent = self.line_indent + 1
				else:
					tokens.append("~")
			elif c == '\u21E9':
				self.sub = True
			elif c == '\u21E7':
				self.sup = True
			elif c == '\u2759':
				self.bold = True
			else:
				if self.start_of_line:
					self.start_of_line = False
					self.markLine()
					if self.line_indent > 0:
						tokens.append("\hspace*{{{}em}}".format(self.line_indent*0.5))
				
				if self.sub:
					data_clean += "\\textsubscript{"
				if self.sup:
					data_clean += "\\textsuperscript{"
				if self.bold:
					data_clean += "{\\boldmath\\bfseries{"
				
				if c == '_':
					data_clean += "$\_$"
				elif c == '\\':
					data_clean += "{\\textbackslash}"
				elif c == '&':
					data_clean += "\\&"
				elif c == '$':
					data_clean += "$\$$"
				elif c == '{':
					data_clean += "\\{"
				elif c == '}':
					data_clean += "\\}"
				elif c == '%':
					data_clean += "\\%"
				elif c == '#':
					data_clean += "\#"
				elif c == '^':
					data_clean += "\\^{}" # TODO
				else:
					if c in unicode_map:
						data_clean += "{{\\pidesym{}}}".format(unicode_map[c])
					else:
						data_clean += c

				if self.sub:
					data_clean += "}"
					self.sub = False
				if self.sup:
					data_clean += "}"
					self.sup = False
				if self.bold:
					data_clean += "}}"
					self.bold = False
		if len(data_clean) > 0:
			tokens.append(data_clean)
		content = ""
		for token in tokens:
			content = content + "{{{}}}".format(token)
		print(content, end="")
		if specialAntiquote:
			print("\\end{pidespecialantiquote}", end="")
		if self.is_plain_text:
			self.is_plain_text = False
			if self.is_section:
				print("\\addtocounter{{subsection}}{{1}}\\addcontentsline{{toc}}{{subsection}}{{\\protect\\numberline{{\\thesubsection}} {}}}".format(content.replace('‹', '').replace('›','')), end="")
				self.is_section = False
		

theories = [
	('AOT', 'AOT_model', 'Model for the Logic of AOT'),
	('AOT', 'AOT_commands', 'Outer Syntax Commands'),
	('AOT', 'AOT_syntax', 'Approximation of the Syntax of PLM'),
	('AOT', 'AOT_semantics', 'Semantics'),
	('AOT', 'AOT_Definitions', 'Definitions of AOT'),
	('AOT', 'AOT_Axioms', 'Axioms of AOT'),
	('AOT', 'AOT_PLM', 'The Deductive System PLM'),
	('AOT', 'AOT_BasicLogicalObjects', 'Basic Logical Objects'),
	('AOT', 'AOT_RestrictedVariables', 'Restricted Variables'),
	('AOT', 'AOT_ExtendedRelationComprehension', 'Extended Relation Comprehension'),
	('AOT', 'AOT_PossibleWorlds', 'Possible Worlds'),
	('AOT', 'AOT_NaturalNumbers', 'Natural Numbers'),
	('AOT', 'AOT_misc', 'Additional Theorems')
]

blobs = [
#        ('AOT_keys.ML', 'AOT$\_$keys.ML: PLM Key Mapping'),
        ('AOT_commands.ML', 'AOT$\_$commands.ML: Outer Syntax Command'),
        ('AOT_syntax.ML', 'AOT$\_$syntax.ML: Syntax Helpers')
]

referenceChecker = ReferenceChecker(theories)
for (session,thy,title) in theories:
	file = open('./pide_markup/' + session + "." + thy + '.xml', mode='r')
	content = file.read()
	referenceChecker.feed(content)

print("\\nolinenumbers")
print("\\chapter{Isabelle Theory}")
section = 0
for (session,thy,title) in theories:
	section = section + 1
	file = open('./pide_markup/' + session + "." + thy + '.xml', mode='r')
	content = file.read()
	print("\\nolinenumbers")
	print("\\section{{{}}}".format(title))
	print("\\label{{{}:{}}}".format(session, thy))
	print("\\resetlinenumber")
	print("\\begin{linenumbers}")
	parser = PideXMLParser(thy, "A", section)
	parser.feed(content)
	print("\\end{linenumbers}")
	print("\\newpage")

addBlobs = False
if addBlobs:
	print("\\nolinenumbers")
	print("\\chapter{ML Helpers}")
	for (blob,title) in blobs:
		file = open('./pide_markup/' + blob + '.xml', mode='r')
		content = file.read()
		print("\\nolinenumbers")
		print("\\section{{{}}}".format(title))
		print("\\label{{{}}}".format(blob))
		print("\\resetlinenumber")
		print("\\begin{linenumbers}")
		parser.setTheory(blob)
		parser.feed(content)
		print("\\end{linenumbers}")
		print("\\newpage")
