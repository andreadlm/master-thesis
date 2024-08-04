# A LEAN-certified reversibilization of Meyer-Ritchie LOOP language

## Configuring

## Building
To build the project run
```
lake build
```

To build the executable run
```
lake build l2s
```

## Running
To execute the compiler from the command line run:

```
lake exe l2s -o <output_file> <input_file>
```

or directly, after building the executable:
```
cd .lake\build\bin
.\l2s -o <output_file> <input_file>
```
## Building the docs
To build the documentation run:
```
lake -Kdoc=on update
lake -Kdoc=on build MasterThesis:docs
```
The root of the built docs will be `.lake/build/doc/index.html`.
