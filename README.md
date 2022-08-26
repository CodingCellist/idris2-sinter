# idris2-sinter

A [sinter](https://www.magnostherobot.co.uk/git.cgi/5th-year-coursework/sinter/)
backend for [Idris2](https://github.com/idris-lang/idris2).

Created during the 2021 Idris2 Developer's Meeting.

# Building an Executable Using this Backend

This backend does not (yet) produce an executable: instead, it produces Sinter
code, which can be compiled by `sinc`.

Steps to build an executable:
1. Build this compiler backend:
```shell
sirdi build
```
2. Use this backend to compile your desired program:
```shell
./build/exec/main -o out.sin <input_source>
```
3. Copy the produced file into the `make` directory:
```shell
cp ./build/exec/out.sin make/program.sin
```
4. `cd` into the `make` folder and run `make`.

The following is required for the above steps to work:
- the Boehm garbage collector;
- LLVM (10 by deafult, 14 if you're using the `mag/llvm-14` branch of `sinc`);
- `sinc` (provided by the Sinter repository linked above);
- `clang`.
