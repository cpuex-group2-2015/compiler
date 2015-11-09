# Powerless PC Compiler

CPU実験2015

## Build
```sh
> make
```

min-camlが生成されます

## 実行
```sh
> ./min-caml target
```

Four files will be generated in folder 'result'.
- target.s is an assembler text file
- target.bin is the whole binary file
- target.data is the data only binary file
- target.zero is the pseudo-binary text file


