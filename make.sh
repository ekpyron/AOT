#!/bin/sh -e
isabelle build -e -D .
./export_pide_markup.scala
./pide_to_latex.py > thesis/theories.tex
isabelle build -e -D thesis
