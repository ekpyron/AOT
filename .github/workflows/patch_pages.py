#!/usr/bin/env python3

import sys;
import glob;
import re;
import os;

source_start='<pre class="source">';
source_end='</pre>\n';

theorems = {}

symbols = {}
with open(os.path.join(os.path.dirname(os.path.realpath(__file__)), "symbolmap")) as f:
  for line in f.readlines():
    split = line.strip().split()
    symbols[split[0]] = line[len(split[0]):].strip()

symbolPattern = re.compile("|".join(map(re.escape, symbols.keys())))

with open(os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..","AOT.ExportInfo","info")) as f:
  for line in f.readlines():
    split = line.strip().split('|')
    items = " ".join(map(lambda i: "("+i+")",split[2].split()))
    if len(split[1]) > 1:
      theorems["{}.{}".format(split[0],split[1])] = items
      theorems[symbolPattern.sub(lambda m: symbols[m.group(0)], split[1])] = items
theoremPattern = re.compile(r'id=["]({})[|]([^"]*)["]'.format("|".join(map(re.escape, theorems.keys()))))
linkPattern = re.compile(r'href=["]([^"#]*)#({})[|]([^"]*)["]'.format("|".join(map(re.escape, theorems.keys()))))

for filename in sys.argv[1:]:
  print("Patching: " + filename)
  output=""
  with open(filename, 'r') as f:
    source=False;
    i = 1;
    for line in f.readlines():
      if source:
        if line.endswith(source_end):
          source=False;
        output += '<a name="L{}" href="#L{}"><span class="linenumber">{}</span></a>{}'.format(i,i,i,line);
        i = i + 1
      elif line.startswith(source_start):
        source=True;
        output += '{}<a name="L{}" href="#L{}"><span class="linenumber">{}</span></a>{}'.format(source_start, i, i, i, line[len(source_start):]);
        i = i + 1
      else:
        output += line;
        if line.startswith('<body>'):
          output+='''<!--
Github corner taken from: https://github.com/tholman/github-corners/
Licensed as:

The MIT License (MIT)

Copyright (c) 2016 Tim Holman

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//-->
<a href="https://github.com/ekpyron/AOT" class="github-corner" aria-label="View source on GitHub"><svg 
width="80" height="80" viewBox="0 0 250 250" style="fill:#151513; color:#fff; position: fixed; top: 0; border: 
0; right: 0;" aria-hidden="true"><path d="M0,0 L115,115 L130,115 L142,142 L250,250 L250,0 Z"></path><path 
d="M128.3,109.0 C113.8,99.7 119.0,89.6 119.0,89.6 C122.0,82.7 120.5,78.6 120.5,78.6 C119.2,72.0 123.4,76.3 
123.4,76.3 C127.3,80.9 125.5,87.3 125.5,87.3 C122.9,97.6 130.6,101.9 134.4,103.2" fill="currentColor" 
style="transform-origin: 130px 106px;" class="octo-arm"></path><path d="M115.0,115.0 C114.9,115.1 118.7,116.5 
119.8,115.4 L133.7,101.6 C136.9,99.2 139.9,98.4 142.2,98.6 C133.8,88.0 127.5,74.4 143.8,58.0 C148.5,53.4 
154.0,51.2 159.7,51.0 C160.3,49.4 163.2,43.6 171.4,40.1 C171.4,40.1 176.1,42.5 178.8,56.2 C183.1,58.6 
187.2,61.8 190.9,65.4 C194.5,69.0 197.7,73.2 200.1,77.6 C213.8,80.2 216.3,84.9 216.3,84.9 C212.7,93.1 
206.9,96.0 205.4,96.6 C205.1,102.4 203.0,107.8 198.3,112.5 C181.9,128.9 168.3,122.5 157.7,114.1 C157.9,116.9 
156.7,120.9 152.7,124.9 L141.0,136.5 C139.8,137.7 141.6,141.9 141.8,141.8 Z" fill="currentColor" 
class="octo-body"></path></svg></a><style>.github-corner:hover .octo-arm{animation:octocat-wave 560ms
ease-in-out}@keyframes
octocat-wave{0%,100%{transform:rotate(0)}20%,60%{transform:rotate(-25deg)}40%,80%{transform:rotate(10deg)}}@medi
a (max-width:500px){.github-corner:hover .octo-arm{animation:none}.github-corner
.octo-arm{animation:octocat-wave 560ms ease-in-out}}</style>

<style>
pre .linenumber {
  float:left;
  margin:0 1em 0 -1em;
  border-right:1px solid;
  text-align:right;
  color: black;
  width: 3em;
  -webkit-touch-callout: none;
  -webkit-user-select: none;
  -khtml-user-select: none;
  -moz-user-select: moz-none;
  -ms-user-select: none;
  -o-user-select: none;
  user-select: none;
}

pre .linenumber span {
  display:block;
  padding:0 .5em 0 1em;
}
</style>
'''

  output = theoremPattern.sub(lambda m: 'id="{}|{}" title="{}"'.format(m.group(1), m.group(2), theorems[m.group(1)]), output)
  output = linkPattern.sub(lambda m: 'href="{}#{}|{}" title="{}"'.format(m.group(1), m.group(2), m.group(3), theorems[m.group(2)]), output)

  with open(filename, 'w') as f:
    f.write(output);

