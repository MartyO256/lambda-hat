# λ^-calculus

An OCaml implementation of the λ^-calculus of G. Barthe et al. from ["Type-based termination of recursive definitions"](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/typebased-termination-of-recursive-definitions/6E6C5061E0C54702E08BD142C0B7BFCB#.Y5_IzRwEAVk.link).

Realized as part of coursework in COMP 762, Fall 2022.

## Getting Started

Install the OCaml package manager ([`opam`](http://opam.ocaml.org/)) by following the instructions at <http://opam.ocaml.org/doc/Install.html>.
Then, download, build and execute the REPL from a local `opam` switch:

```bash
git clone https://github.com/MartyO256/lambda-hat.git lambda-hat
cd lambda-hat
opam switch create . --deps-only --with-test --yes
eval $(opam env)
dune exec lambda_hat_repl
```

Here is an example REPL session:

```txt
In  [1]: datatype Nat =
           | O : Nat
           | S : Nat -> Nat;;
Out [1]: <datatype>

In  [2]: let plus =
           letrec plus : Nat^i -> Nat -> Nat =
             \x : Nat^$i. \y : Nat. case x of {
               | O => y
               | S => \x' : Nat^i. S (plus x' y)
             };;
Out [2]: <value>

In  [3]: let q = plus (S (S (S O))) (S O);;
Out [3]: val q = S (S (S (S O)))
```

**Note:** Issues in the typing algorithm prevent some programs from the [`examples/examples.mu`](./examples/examples.mu) file from being accepted.
