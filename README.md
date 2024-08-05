# A LEAN-certified reversibilization of Meyer-Ritchie LOOP language
University of Turin, master thesis in computer science.

## Documentation
The full documentation of the project can be read [here](https://andreadlm.github.io/master-thesis/) and is generated automatically from the source `.lean` files.

## Configuring

## Building
To build the project run
```sh
lake build
```

To build the executable run
```sh
lake build l2s
```

### Building the docs
To build the documentation run:
```sh
lake build MasterThesis:docs
```
The root of the built docs will be `.lake/build/doc/index.html`.

## Running
To execute the compiler from the command line run:

```sh
lake exe l2s -o <output_file> <input_file>
```

or directly, after building the executable:
```sh
cd .lake\build\bin
.\l2s -o <output_file> <input_file>
```
