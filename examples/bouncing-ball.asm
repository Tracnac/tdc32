; A monochrome 8x8 ball bouncing inside the 640x480 screen edges.
; Coordinates use an 80x60 grid of 8x8-pixel cells.
; The VM's frame counter paces movement at one cell per VBL.
; Load, Reset / Assemble, then Run at Max speed.
.adr $00001000
.code start
ld r8, 40                 ; x cell: 0..79
ld r9, 30                 ; y cell: 0..59
ld r10, 1                 ; x direction: +1 or -1
ld r11, 1                 ; y direction: +1 or -1
ld r3, $FF
bsr paint_ball            ; draw initial ball
ld r6, $0208(R0)          ; current VBL count

:frame_wait
ld r7, $0208(R0)
cmp r7, r6
beq frame_wait
ld r6, r7

ld r3, 0
bsr paint_ball            ; erase old position
add r8, r10
cmp r8, 0
beq bounce_left
cmp r8, 79
beq bounce_right
ba update_y
:bounce_left
ld r10, 1
ba update_y
:bounce_right
ld r10, $FFFF
ldu r10, $FFFF

:update_y
add r9, r11
cmp r9, 0
beq bounce_top
cmp r9, 59
beq bounce_bottom
ba draw_new
:bounce_top
ld r11, 1
ba draw_new
:bounce_bottom
ld r11, $FFFF
ldu r11, $FFFF

:draw_new
ld r3, $FF
bsr paint_ball
ba frame_wait

; Paint an 8x8 round sprite, one packed byte per scanline.
; Inputs: R8=x cell, R9=y cell, R3=draw mask ($FF) or erase mask (0).
:paint_ball
ld r1, (screen_base)
ld r2, r9
mul r2, 640                ; 8 scanlines * 80 bytes per scanline
add r2, r8                 ; x cell is also the byte column
add r1, r2
ld r2, ball_bitmap
ld r4, 8
:paint_row
ldb r5, (r2)
and r5, r3
stb (r1), r5
add r1, 80
add r2, 1
sub r4, 1
bne paint_row
rts

.adr $00004000
.data screen_base
.u32 $00010000
.data ball_bitmap
.u8 $18, $3C, $7E, $7E, $7E, $7E, $3C, $18
