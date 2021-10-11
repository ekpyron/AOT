#!/usr/bin/env python3
file = open('./thesis/theories.tex')
content = file.read()
for x in content:
	if ord(x) > 0x80:
		print("UNICODE CHAR: ", x, "{0:04x}".format(ord(x)))
