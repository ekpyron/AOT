#!/usr/bin/env python3
from html.parser import HTMLParser
import sys

keys = {}

with open("./keys.list") as f:
	for line in f.readlines():
		split = line.strip().split('|')
		keys[split[1]] = split[0]

class PideXMLParser(HTMLParser):
	def __init__(self):
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

	def handle_starttag(self, tag, attrs):
		endtagfuns = []
		if tag == "entity":
			refname = None
			defname = None
			name = None
			is_fact = False
			is_command = False
			for (attr,value) in attrs:
				if attr == "def":
					defname = value
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
			if defname:
				self.defs[defname] = defname
				endtagfuns.append(lambda self: print("}", end=""))
				print("\\myhypertarget{{{}}}{{".format(defname), end="")
				if name and is_fact:
					name = name.split('.')[-1]
					self.defsByName[name] = defname
					name = name.split('[')[0]
					name = name.split(':')
					if name[0] in keys:
						self.current_def = keys[name[0]]
						for s in name[1:]:
							self.current_def += '.' + s
			elif refname and refname in self.defs:
				endtagfuns.append(lambda self: print("}", end=""))
				print("\\hyperlink{{{}}}{{".format(self.defs[refname]), end="")
			elif refname and name:
				name_parts = name.split('.')
				if len(name_parts) > 1 and name_parts[-2].endswith("_class") and name_parts[-1] in self.defsByName:
					print("\\hyperlink{{{}}}{{".format(self.defs[self.defsByName[name_parts[-1]]]), end="")
					endtagfuns.append(lambda self: print("}", end=""))
		elif tag == "plain_text":
			self.is_plain_text = True
		self.endtagfuns.append(endtagfuns)
		print("\\begin{{{}}}".format("isa"+tag), end="")

	def handle_endtag(self, tag):
		print("\\end{{{}}}".format("isa"+tag), end="")
		for fun in self.endtagfuns.pop():
			fun(self)

	def handle_data(self, data):
		tokens = []
		data_clean = ""
		for c in data:
			if c == "\n":
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
					data_clean += "\{"
				elif c == '}':
					data_clean += "\}"
				elif c == '%':
					data_clean += "\\%"
				elif c == '#':
					data_clean += "\#"
				elif c == '^':
					data_clean += "\\^{}" # TODO
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
		if self.is_plain_text:
			self.is_plain_text = False
			if self.is_section:
				print("\\addtocounter{{subsection}}{{1}}\\addcontentsline{{toc}}{{subsection}}{{\\protect\\numberline{{\\thesubsection}} {}}}".format(content.replace('‹', '').replace('›','')), end="")
				self.is_section = False
		

parser = PideXMLParser()

theories = [
	('AOT.AOT_model', 'Model for the Logic of AOT'),
	('AOT.AOT_commands', 'Outer Syntax Commands'),
	('AOT.AOT_syntax', 'Approximation of the Syntax of PLM'),
	('AOT.AOT_semantics', 'Semantics'),
	('AOT.AOT_Definitions', 'Definitions of AOT'),
	('AOT.AOT_Axioms', 'Axioms of AOT'),
	('AOT.AOT_PLM', 'The Deductive System PLM'),
	('AOT.AOT_BasicLogicalObjects', 'Basic Logical Objects'),
	('AOT.AOT_RestrictedVariables', 'Restricted Variables'),
	('AOT.AOT_ExtendedRelationComprehension', 'Extended Relation Comprehension'),
	('AOT.AOT_PossibleWorlds', 'Possible Worlds'),
	('AOT.AOT_NaturalNumbers', 'Natural Numbers')
]

blobs = [
#        ('AOT_keys.ML', 'AOT$\_$keys.ML: PLM Key Mapping'),
        ('AOT_commands.ML', 'AOT$\_$commands.ML: Outer Syntax Command'),
        ('AOT_syntax.ML', 'AOT$\_$syntax.ML: Syntax Helpers')
]

print("\\nolinenumbers")
print("\\chapter{Isabelle Theory}")
for (thy,title) in theories:
	file = open('./pide_markup/' + thy + '.xml', mode='r')
	content = file.read()
	print("\\nolinenumbers")
	print("\\section{{{}}}".format(title))
	print("\\resetlinenumber")
	print("\\begin{linenumbers}")
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
		print("\\resetlinenumber")
		print("\\begin{linenumbers}")
		parser.feed(content)
		print("\\end{linenumbers}")
		print("\\newpage")
