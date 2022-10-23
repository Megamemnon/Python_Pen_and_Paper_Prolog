# Python Pen & Paper Prolog
A Python implementation of Prolog using character strings to hold and work with clauses and terms instead of a syntax tree. No lexer; no parser. Just 400 lines of Python, including comments. "Pen & Paper" is a reference to Pen and Paper RPGs, as opposed to computer RPGs. PPPP does Prolog much like you might do it with pen and paper.

Python is much more elegant than C. I wrote this after writing [Pen & Paper Prolog in C](https://github.com/Megamemnon/Pen_and_Paper_Prolog), dealing with pointer arithmetic, allocation and garbage collection, etc. 

Unlike the C version, I have no intention of enabling line editing in this Python version. It's been my intention to use a small Prolog-like-engine as a proof assistant because I love the separation of syntax and semantics in pure Prolog as well as the absence of a need to have the code actually DO anything. Having played with this and compared results to Ciao and SWIPL, I now realize Prolog is mostly unsuited to this (I had read as much but felt compelled to try anyway). I think the key to making this work would be to define a 'proof' as a selection of facts and rules (a scoped portion of a larger database/knowledgebase) and one or more queries. I'm constantly running into infinite loops, or deeper depths than I'm willing to outwait, when running a query on a small knowledgebase written in the fashion I plan on using.

Some notes to take the place of a proper readme:

- input file can include blank lines and comments, but comments must be the full line (i.e. line must start with '%' as first character).
- first argument after the program name on the command line is expected to be a 'prolog' file; if no file is provided, pppp will attempt to load a file named 'testkb'
- a second command may be entered on command line (after prolog filename) and is expected to be a query (enclosed in quotes). For example: python pppp.py testkb "?-nat(succ(0))." . When a query is provided in this fashion, pppp will display only the first result and then exit.
- Variables can represent functors and not just atoms. Use wisely.
