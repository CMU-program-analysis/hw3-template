# Instructions

- Install [opam](https://opam.ocaml.org/doc/Install.html) (these instructions
  assume opam version 2+)
- Create a new switch (you can replace "homework" with any switch name you'd like):
```
opam init
opam switch create homework 4.09.0
eval $(opam env)
```
- Install dependencies:
```
opam install core dune merlin ounit2
```
- Build with `make`. This will create symlinks to four binaries. They are:
    - `while`: a While interpreter
    - `w3a`: a While3addr interpreter
    - `compile`: a While to While3addr compiler
    - `analyze`: analyzes a While3addr file (using your analysis) and outputs
      the results
  All of these binaries take input on stdin and output on stdout (i.e., you can
  run a While program by running `./while < program.while`, *not* by passing a
  file as input).
  
 - Test with `make test`. This will run any test cases placed in `test/test_analysis.ml`. There are a few test cases      already provided in the `test_analysis.ml` file to help you get started with testing your code, and we highly suggest that
   you add more!

# Handin
Handin *only* `src/analysis/df.ml` to Gradescope to run your code against a set of held out test cases.

# Resources

- You might be interested in reading Adam Chlipala's overview of the philosophic
  differences between OCaml and SML: http://adam.chlipala.net/mlcomp/
- This page has a nice side-by-side comparison of the syntax of SML and OCaml:
  https://people.mpi-sws.org/~rossberg/sml-vs-ocaml.html
- We are using the [Core library](https://ocaml.janestreet.com/ocaml-core/latest/doc/base/Base/index.html)
  maintained by Jane Street as it is more feature-rich than the OCaml standard
  library. The API documentation on that page should be useful.
- If you're using Vim or Emacs, [Merlin](https://ocaml.github.io/merlin/) is a
  very useful tool that adds features like autocompletion and function signature
  lookup. The [Merlin GitHub page](https://github.com/ocaml/merlin) will help
  you get set up.
- If you're using Emacs, [Tuareg mode](https://github.com/ocaml/tuareg) is a
  good editing mode.
- OCaml is a compiled or interpreted language, so it can be run in a
  [REPL](https://en.wikipedia.org/wiki/Read%E2%80%93eval%E2%80%93print_loop). You
  can use the standard OCaml REPL, but we recommend
  [UTop](https://opam.ocaml.org/blog/about-utop/), which can be installed with
  `opam install utop`.
- The [official OCaml site](https://ocaml.org/learn/) has a lot of
  resources for learning OCaml.
- [Real World OCaml](https://realworldocaml.org/) is a great book for learning
  OCaml and is available free online.
