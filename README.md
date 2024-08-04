# A LEAN-certified reversibilization of Meyer-Ritchie LOOP language

## Build
To build the project run
```
lake build
```

To build the executable run
```
lake build l2s
```

## Run
To execute the compiler from the command line run:

```
lake exe l2s -o <output_file> <input_file>
```

or directly, after building the executable:
```
cd .lake\build\bin
.\l2s -o <output_file> <input_file>
```



