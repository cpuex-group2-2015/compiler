	mfftg	r2, f0		# int_of_float_sub
	mfftg	r5, f0		# f0 -> r2
	li	r6, 9
	sl	r2, r2, r6
	sr	r2, r2, r6
	li	r6, 1
	sl	r5, r5, r6
	li	r6, 24
	sr	r5, r5, r6
	lis	r6, 0b0000000010000000
	add	r2, r2, r6
	subi	r5, r5, 140
	cmp	r5, r0
	blt	_first_label
	sl	r2, r2, r5
	neg	r5, r5		# _first_label
	sr	r2, r2, r5
	blr
	mr	r6, r2		# create_array
	mr	r2, r4		# r2 r5 -> r2
	cmp	r6, r0		# _array_loop
	beq	_second_label
	st	r5, 0(r4)
	addi	r4, r4, 4
	subi	r6, r6, 1
	b	_array_loop
	blr			# _second_label
	mr	r6, r2		# create_float_array
	mr	r2, r4
	mfftg	r5, f0
	b	_array_loop
	sl	r6, r6, r2	# float_of_int_sub
	li	r2, 0		# r2 r5 r6 -> f0
	li	r7, 23
	sl	r5, r5, r7
	or	r2, r5, r2
	or	r2, r6, r2
	mfgtf	f0, r2
	blr
	recv	r2		# read_int
	blr
	recv	r2		# read_float
	mfgtf	f0, r2
	blr
	send	r2		# print_char
	blr
