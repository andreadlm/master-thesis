# A Lean-certified reversibilization of Meyer-Ritchie LOOP language
University of Turin, master thesis in computer science.

This project introduces the Lean formalization of SCORE, a minimal reversible programming language 
designed as a reversible adaptation of Meyer and Ritchie's LOOP language. SCORE can be understood as 
an extension of Matos' SRL language with native support for stacks. The language is _reversible_, 
meaning that for every program, it is possible to compute the inverse program using a syntax-directed 
inversion function. The operational semantics of the language is defined through an interpreter and
its invertibility property is proved. Additionally, the project provides a formal proof that two 
compilers, one a generalization of the other, transform any LOOP program into an equivalent SCORE 
program.

## Documentation
The full documentation of the project can be read [here](https://andreadlm.github.io/master-thesis/) 
and is generated automatically from the source `.lean` files.

## Configuring
After downloading the project, run
```shell
lake update
```
to download/update all the dependecies.

## Building
To build the project run
```shell
lake build
```

To build the executable run
```shell
lake build l2s
```

### Building the docs
To build the documentation run:
```shell
lake build MasterThesis:docs
```
The root of the built docs will be `.lake/build/doc/index.html`.

## Running
To execute the compiler from the command line run:

```shell
lake exe l2s -o <output_file> <input_file>
```

or directly, after building the executable:
```shell
cd .lake\build\bin
.\l2s -o <output_file> <input_file>
```
