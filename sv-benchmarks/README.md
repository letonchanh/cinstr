```
gcc -o sv.o -c sv.c
gcc s3_clnt_3.BV.c.cil-2a.c.instr.c sv.o
```

```
gcc -shared -o libsv.so sv.o -lm
gcc s3_clnt_3.BV.c.cil-2a.c.instr.c -L/Users/chanhle/repo/cinstr/sv-benchmarks -lsv
```

(https://www.cs.swarthmore.edu/~newhall/unixhelp/howto_C_libraries.html)
