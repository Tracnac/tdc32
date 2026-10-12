; Poll the virtual-computer keyboard and VBL frame counter.
; Inspect $00004000-$00004007 in the Memory panel while running.
.adr $00001000
.code io_board_test
:poll
ld r1, $0200(R0)
st keys_seen(R0), r1
ld r2, $0208(R0)
st frames_seen(R0), r2
ba poll

.adr $00004000
.data keys_seen
.u32 0
.data frames_seen
.u32 0
