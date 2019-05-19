
# MtE 0.90b

this is probably my favourite polymorphic engine from the dos era, and the
one that kicked off a trend of releasing engines as an obj (tpe, ned, etc).
this is a byte-for-byte match of the binary, but unfortunately i couldn't
find TASM 2.5 to get an identical build of the .OBJ.  To assemble:

  ```
  > tasm /w+ /v /m mte
  > tlink /x /t demovir rnd mte
  ```

it took several hours to pull this apart, as the code generation strategy and
phases weren't immediately obvious without sticking breakpoints into the
code.  this was made difficult with traditional tools (i.e. debug.exe) by MtE
requiring an INT 3 handler for tracing during its garbage generation to 
insert a (TEST+)JNZ payload.  most of the memory references to the scratch
area throughout the code are done indirectly via [di], i've applied the delta
to clarify the target of the reference.  this might seem a little awkward
with '(ops - ops)[si]', but let's err on the side of readability.

## summary of the op table

id | op
--- | ---
0 | data
1 | start/end
2 | pointer
3 | sub *
4 | add *
5 | xor *
6 | mul *
7 | rol *
8 | ror *
9 | shl
A | shr
B | or
C | and
D | imul
E | jnz

\* ops 3 to 8 used for the crypt ops only

when an argument (ops_args) is 0, the pointer reg will be used instead.

some optimizations (see try_optimization) are made for generated code with
ADD/SUB reg,[-2,2] into INC/DEC reg.  impressively, this is also done for "XOR
reg,-1" into NOT, and is the only time MtE generates NOT.

structure is as follows:
1. intro junk ops, init pointer reg
2. crypt operations
3. (this code has no impact, apart from when we pick the ptr register)
    1. post crypt ops junk
    2. inverse
4. inc/inc ptr, unless an add/sub op on the ptr was adjusted in [3(ii)]
5. jnz [2]
6. outro junk ops

enjoy!
