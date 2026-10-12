# TDC32.01 Toolchain Specification

This document describes the current TDC32 assembler syntax and source-file conventions. Instruction semantics and encodings are defined in [TDC32-1.md](TDC32-1.md). Memory placement, loading, and startup behavior are platform-specific and defined in [VM32-1.md](VM32-1.md).

## Source format

- One instruction or directive per line.
- Labels are declared on their own line as `:name`; labels are case-insensitive.
- A semicolon (`;`) starts a comment outside a quoted string.
- Numeric literals are decimal, `$`-prefixed hexadecimal, or `%`-prefixed binary. Underscores in numbers are ignored. The old `0x`, `0b`, and `0o` prefixes are not accepted.
- The default assembly origin is supplied by the virtual-computer loader. In the current VM32 implementation, it is `$00000400`; `.adr` can select another supported location.

## Directives

Directives are assembler conveniences, not CPU instructions.

| Directive | Meaning |
| --- | --- |
| `.adr address` | Set the assembly location counter. Subsequent code or data is assembled there. |
| `.align n` | Advance the location counter to the next address divisible by positive byte alignment `n`; no bytes are emitted. |
| `.code name` | Define a code label at the current location; the location must satisfy the platform's executable-RAM and alignment requirements. |
| `.data name` | Define a data label at the current location; it does not itself reserve storage. |
| `.str "text"` | Emit quoted US-ASCII bytes without a terminator. Non-ASCII characters are rejected. |
| `.u8 value[, ...]` | Emit unsigned byte values (0–255). |
| `.u16 value[, ...]` | Emit unsigned 16-bit values in big-endian byte order (0–65535). |
| `.u32 value[, ...]` | Emit unsigned 32-bit values in big-endian byte order (0–4294967295). |

Data directives emit values consecutively without automatic padding. Labels name the address of the next emitted byte. `.align` advances the location counter but emits no data. Within data expressions, `$` alone denotes the current location counter; `($ - label)` evaluates the byte distance from `label` to the current data address. For example, after `.data hello`, `.str "A"`, `.align 4`, and `.u32 $FFFFFFFF`, `.u8 ($ - hello)` emits `8`. `.str` emits exactly its string bytes and does not append a zero byte. Forward label references are accepted where the operand or data expression permits them.

The assembler rejects code/data emission into locations the current platform does not expose for that purpose. See [VM32-1.md](VM32-1.md) for the current system-page and memory map.

## Symbolic instruction operands

Labels used by instructions are resolved relative to the address of the current instruction unless the form explicitly uses R0 as an absolute base. Displacements are byte offsets and must fit the encoded signed 16-bit field where applicable.

### Loads

- `LD Rd, label` loads the address of `label` using a signed PC-relative byte displacement.
- `LD Rd, (label)` loads a word from `label` using a signed PC-relative byte displacement. The label must be word-aligned.
- `LD Rd, label(Rs)` uses `label - instruction-PC` as a signed byte displacement when `Rs` is not R0. With `R0` as the base, the label address is an absolute byte offset.
- `LD Rd, (Rs)` loads from the address in `Rs`.
- `LDB` and `LDSB` use the same symbolic memory forms as `LD`, without word-alignment requirements. `LDH` and `LDSH` use those forms with 2-byte alignment.

### Stores

- `ST (label), Rvalue` stores at `label` using a signed PC-relative byte displacement. The label must be word-aligned.
- `ST label(Rbase), Rvalue` uses `label - instruction-PC` as a signed byte displacement when `Rbase` is not R0. With R0 as the base, the label address is an absolute byte offset. `ST label(PC), Rvalue` stores directly to the label.
- `STB (label), Rvalue` uses the same PC-relative form without an alignment requirement. `STH (label), Rvalue` uses the same form and requires 2-byte alignment.
- `STB label(Rbase), Rvalue` and `STH label(Rbase), Rvalue` use the same symbolic offset rules as `ST label(Rbase), Rvalue`; only STH requires 2-byte alignment.

The encoded ST fields place the address base in `Rs` and the stored value register in `Rd`; the source syntax deliberately puts the address first.

## Pseudo-operations

These source-level aliases expand to ordinary instructions and have no opcodes:

- `INC Rd` expands to `ADD Rd, R0, 1`.
- `DEC Rd` expands to `SUB Rd, R0, 1`.
