#!/bin/bash
if [ $# -ne 1 ]; then
	echo "Usage: $0 [keyfile.aux] > AOT_keys.ML"
	exit 1
fi
if [ ! -e $1 ]; then
	echo "Cannot open key file: $1"
	exit 1
fi
echo -e "val AOT_items = [\n$(cat $1 | grep "{meti.[0-9]*}" | sed -n 's/\\newlabel{\([^}]*\)}.*{meti.\([0-9]*\)}.*/    (\2, "\1"),/p')]" | sed 's/,]/\n]/'
