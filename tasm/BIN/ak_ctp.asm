TITLE	COMP2003 Transmission Protocol Tester
COMMENT |
    COMP2003A Assignment 2 (Fall 2008)
	  Student Name: Alex Kwiatkowski
	  Student ID: 100734913
	  Objective: Simulates a crude network transmission protocol
	    Input: Binary string
	    Output: Contents of binary string
|        



.MODEL SMALL
.STACK 100H

.DATA							; data segment

requestChar1	DB	'Please type a character: ',0
output1			DB	'All done!',0
ip_address_msg	DB	'The IP address is ',0
pre_message_msg	DB	'The message is: "',0
invalid_check	DB	'ERROR: Bad checksum!.',0
dbl_quote_msg	DB	'"',0
period_msg		DB	'.',0
address			DB	4 DUP(?)
message			DB	16 DUP(?),0	; note that the message is also referred to as the "payload" throughout the code
checksum		DW	?

.CODE							; code segment

INCLUDE io.mac
.486

main	PROC                                     
	.STARTUP
	push	OFFSET address
	push	OFFSET message
	push	OFFSET checksum
	call	sipo

	push	OFFSET message
	call	checker

	cmp		AX,checksum
	jne		invalid_checksum

	nwln

	; print IP address
	PutStr	ip_address_msg
	mov		BP,OFFSET address
	mov		SI,4
print_ip_loop:
	xor		AH,AH
	mov		AL,[BP]
	PutInt	AX
	PutStr	period_msg
	inc		BP
	dec		SI
	jnz		print_ip_loop
	
	; print message/payload if the checksum is correct, an error message otherwise
	nwln
	PutStr	pre_message_msg
	PutStr	message
	PutStr	dbl_quote_msg
	nwln
	jmp		end_of_program
invalid_checksum:
	PutStr	invalid_check
	
end_of_program:
	.EXIT
main	ENDP

; Reads a "binary" CTP transmission from the input stream and places its contents into three variables passed in on the stack
sipo	PROC					; serial in, parallel out
	pusha						; 16 bytes are pushed onto the stack
	mov		BP,SP				; BP points at the top of the stack
	add		BP,16h
	mov		BP,[BP]				; now BP points at the third input value (address)

	; Read the STX , 'C', 'T', and 'P' characters
	mov		SI,4
initial_loop:
	call	readChar
	dec		SI
	jnz		initial_loop

	; Read the IP address
	mov		SI,4				; will be reading four bytes
ip_address_loop:
	call	readChar
	mov		[BP],AL
	inc		BP
	dec		SI
	jnz		ip_address_loop

	; Read the payload
	mov		BP,SP				; BP points at the top of the stack
	add		BP,14h
	mov		BP,[BP]				; now BP points at the second input value (message)
payload_loop:
	call	readChar
	cmp		AL,03h				; 03h is end of text (ETX) character
	je		end_of_payload
	mov		[BP],AL
	inc		BP
	jmp		payload_loop
end_of_payload:
	mov		BYTE PTR [BP],0		; zero character to mark the end of the string

	; Read the checksum
	mov		BP,SP				; BP points at the top of the stack
	add		BP,12h
	mov		BP,[BP]				; now BP points at the first input value (checksum)
	call	readChar
	mov		AH,AL
	call	readChar
	mov		[BP],AX
	
	; Read the EOT (end of transmission) character
	call	readChar

	popa						; 16 bytes are popped off the stack
	ret		6					; 3 addresses = address + message + checksum
sipo	ENDP

; Computes the checksum of a string on the stack and returns the value in AX
checker	PROC
	push	BP
	push	SI
	push	CX

	mov		BP,SP				; BP points at the top of the stack
	mov		BX,[BP+8]			; now BP points at the first character of the input string

	xor		AX,AX				; '1' bit counter

checker_loop:
	cmp		[BX],BYTE PTR 0		; until the end of the string is reached
	je		end_checker_loop

	mov		SI,8
	mov		CX,1				; bit mask
	mov		DX,[BX]
checker_bit_loop:
	push	CX
	and		CX,DX
	test	CX,CX				; check is the current bit is a zero
	jz		end_bit_loop
	inc		AX					; we found a '1' bit
end_bit_loop:
	pop		CX
	shl		CX,1
	dec		SI
	jnz		checker_bit_loop
	
	inc		BX
	jmp		checker_loop
end_checker_loop:
	
	mov		SP,BP
	pop		CX
	pop		SI
	pop		BP
	ret		2
checker	ENDP

; Reads 8 characters (only '1' and '0') from the input stream and returns the ASCII value in AL
readChar	PROC
	push	AX					; save the registers we will be using
	push	CX
	push	DX
	push	SI

	mov		SI,8				; loop counter
	mov		AH,1				; int21 "read char" command
	mov		CH,0				; result ASCII
	mov		DH,128				; bit shift mask
rc_loop:
	int		21h					; read a '1' or a '0'
	cmp		AL,48
	je		rc_is_zero			; the bit is a '0', so don't add anything
	or		CH,DH				; othwise add the current power of two
rc_is_zero:
	shr		DH,1
	dec		SI
	jnz		rc_loop

	pop		SI
	pop		DX
	pop		AX
	mov		AL,CH
	pop		CX
	ret
readChar	ENDP

END	main						; end of program
