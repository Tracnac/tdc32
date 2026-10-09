// TDC32.01 architectural CPU core. The browser UI below remains a separate layer.
'use strict';

const TDC32 = (() => {
  const RAM_BYTES = 0x8000, ROM_BASE = 0x8000, ROM_BYTES = 0x8000;
  const SCREEN_BASE = 0x00010000, SCREEN_BYTES = 640 * 480 / 8;
  const FLAG = { Z: 0x0001, N: 0x0002, C: 0x0004, V: 0x0008, I: 0x2000, S: 0x4000, T: 0x8000 };
  const SR_MASK = FLAG.Z | FLAG.N | FLAG.C | FLAG.V;
  const CUSR_MASK = FLAG.T | FLAG.S | FLAG.I | SR_MASK;
  const OPCODE = Object.freeze({
    b: 0b0000000, cmp: 0b0000001, ld: 0b0000010, st: 0b0000011,
    add: 0b0000100, sub: 0b0000101, mul: 0b0000110, div: 0b0000111,
    and: 0b0001000, or: 0b0001001, xor: 0b0001010, rol: 0b0001011,
    ror: 0b0001100, shl: 0b0001101, shr: 0b0001110, swi: 0b0001111,
    fcmp: 0b0010000, ftoi: 0b0010001, itof: 0b0010010, divq: 0b0010011,
    fadd: 0b0010100, fsub: 0b0010101, fmul: 0b0010110, fdiv: 0b0010111,
    fabs: 0b0011000, adc: 0b0011001, sbc: 0b0011010, mulh: 0b0011011,
    asr: 0b0011101, divu: 0b0100000, divqu: 0b0100001, mulhu: 0b0100010,
    rts: 0b0100011, rti: 0b0100100, fneg: 0b0100101,
    push: 0b0100110, pop: 0b0100111, neg: 0b0101000, not: 0b0101001,
    btst: 0b0101010, bset: 0b0101011, bclr: 0b0101100, bchg: 0b0101101,
    mulu: 0b0101110, swph: 0b0101111, swpb: 0b0110000, getb: 0b0110001,
    putb: 0b0110010, ldb: 0b0110011, ldh: 0b0110100, stb: 0b0110101,
    sth: 0b0110110, ldsb: 0b0110111, ldsh: 0b0111000, ldu: 0b0111001
  });
  const OPCODE_NAME = new Map(Object.entries(OPCODE).map(([name, code]) => [code, name]));
  const COND = {
    beq: 0, bne: 1, bcs: 2, bhs: 2, bcc: 3, blo: 3, bmi: 4, bpl: 5,
    bvs: 6, bvc: 7, bhi: 8, bls: 9, bge: 10, blt: 11, bgt: 12, ble: 13,
    bsr: 14, ba: 15, b: 15
  };
  const state = {
    regs: new Uint32Array(16), pc: 0, cycles: 0,
    ram: new DataView(new ArrayBuffer(RAM_BYTES)),
    framebuffer: new DataView(new ArrayBuffer(SCREEN_BYTES)),
    program: [], sourceMap: new Map(), dataImage: [],
    halted: false, trap: null, changedRegs: new Set(), changedMem: new Set(), last: null
  };
  const u32 = n => Number(n) >>> 0;
  const sx = n => n | 0;
  const sign16 = n => (n << 16) >> 16;
  const fmt = n => '$' + u32(n).toString(16).toUpperCase().padStart(8, '0');
  const flags = () => state.regs[13] & SR_MASK;
  const supervisor = () => !!(state.regs[13] & FLAG.S);
  const pcLabel = s => String(s).trim().replace(/^:/, '').toLowerCase();
  function fail(message, vector = 3) { const e = new Error(message); e.vector = vector; throw e; }

  function parseNum(text) {
    const s = String(text).replaceAll('_', '').trim();
    if (/^[+-]?\d+$/.test(s)) return Number(s);
    if (/^\$[\da-f]+$/i.test(s)) return Number('0x' + s.slice(1));
    if (/^%[01]+$/.test(s)) return Number('0b' + s.slice(1));
    return null;
  }
  function register(text) {
    const s = String(text).trim().toLowerCase();
    if (s === 'cusr' || s === 'sr') return 13;
    if (s === 'sp') return 14;
    if (s === 'pc') return 15;
    const m = /^r(\d+)$/.exec(s);
    if (!m) return null;
    const n = Number(m[1]);
    return n >= 0 && n <= 15 ? n : null;
  }
  function splitArgs(s) { return s.split(',').map(x => x.trim()); }
  function cleanLine(s) {
    let quoted = false, escaped = false;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (escaped) { escaped = false; continue; }
      if (quoted && ch === '\\') { escaped = true; continue; }
      if (ch === '"') quoted = !quoted;
      else if (ch === ';' && !quoted) return s.slice(0, i).trim();
    }
    return s.trim();
  }
  function checked16(n, lineNo, mode = 'signed') {
    const valid = mode === 'unsigned'
      ? Number.isInteger(n) && n >= 0 && n <= 0xffff
      : Number.isInteger(n) && n >= -0x8000 && n <= 0x7fff;
    if (!valid) fail(`Line ${lineNo}: immediate is outside the ${mode} 16-bit range`);
    return n;
  }
  function dataArgs(text) {
    const result = []; let token = '', depth = 0, quoted = false, escaped = false;
    const push = () => { if (token.trim()) result.push(token.trim()); token = ''; };
    for (const ch of text) {
      if (escaped) { escaped = false; token += ch; continue; }
      if (quoted && ch === '\\') { escaped = true; token += ch; continue; }
      if (ch === '"') quoted = !quoted;
      if (!quoted && ch === '(') depth++;
      else if (!quoted && ch === ')') depth--;
      if (!quoted && depth === 0 && (ch === ',' || /\s/.test(ch))) push();
      else token += ch;
    }
    push(); return result;
  }
  function expandPseudo(line) {
    const i = line.search(/\s/), op = (i < 0 ? line : line.slice(0, i)).toLowerCase();
    const args = splitArgs(i < 0 ? '' : line.slice(i).trim());
    if (op === 'inc' && args.length === 1) return [`ADD ${args[0]}, R0, 1`];
    if (op === 'dec' && args.length === 1) return [`SUB ${args[0]}, R0, 1`];
    return [line];
  }

  function assemble(source) {
    const labels = new Map(), raw = [], dataImage = [], occupied = new Set();
    let pc = 0, entryPC = null;
    const mappedByte = a => (a >= 0 && a < RAM_BYTES) || (a >= SCREEN_BASE && a < SCREEN_BASE + SCREEN_BYTES);
    function reserve(address, width, lineNo) {
      if (!Number.isInteger(address) || address < 0 || address + width - 1 > 0xffffffff)
        fail(`Line ${lineNo}: invalid address`);
      for (let i = 0; i < width; i++) {
        const at = address + i;
        if (!mappedByte(at)) fail(`Line ${lineNo}: address ${fmt(at)} is not mapped RAM or video memory`);
        if (occupied.has(at)) fail(`Line ${lineNo}: address ${fmt(at)} is already occupied`);
      }
      for (let i = 0; i < width; i++) occupied.add(address + i);
    }
    function defineLabel(name, address, lineNo) {
      if (!/^[\w.$]+$/.test(name)) fail(`Line ${lineNo}: invalid label “${name}”`);
      const key = name.toLowerCase();
      if (labels.has(key)) fail(`Line ${lineNo}: duplicate label ${name}`);
      labels.set(key, address);
    }
    function labelValue(name, lineNo) {
      const key = pcLabel(name);
      if (!labels.has(key)) fail(`Line ${lineNo}: unknown label “${name}”`);
      return labels.get(key);
    }
    function addInstruction(line, lineNo) {
      for (const expanded of expandPseudo(line)) {
        if ((pc & 3) || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: instruction must be word-aligned in installed RAM`);
        reserve(pc, 4, lineNo);
        raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
        if (entryPC === null) entryPC = pc;
        pc += 4;
      }
    }
    for (const [idx, original] of String(source).split(/\r?\n/).entries()) {
      const lineNo = idx + 1, line = cleanLine(original);
      if (!line) continue;
      const lm = /^:([\w.$]+)$/.exec(line);
      if (lm) { defineLabel(lm[1], pc, lineNo); continue; }
      const ix = line.search(/\s/), op = (ix < 0 ? line : line.slice(0, ix)).toLowerCase();
      const rest = ix < 0 ? '' : line.slice(ix).trimStart(), words = dataArgs(rest);
      if (op === '.adr') {
        if (words.length !== 1) fail(`Line ${lineNo}: .adr syntax is .adr address`);
        const n = parseNum(words[0]);
        if (!Number.isInteger(n) || n < 0 || n > 0xffffffff) fail(`Line ${lineNo}: expected a 32-bit address`);
        pc = n; continue;
      }
      if (op === '.align') {
        if (words.length !== 1) fail(`Line ${lineNo}: .align syntax is .align byte-alignment`);
        const n = parseNum(words[0]);
        if (!Number.isInteger(n) || n <= 0 || n > 0xffffffff) fail(`Line ${lineNo}: .align requires a positive 32-bit alignment`);
        pc = Math.ceil(pc / n) * n;
        if (!Number.isSafeInteger(pc) || pc > 0xffffffff) fail(`Line ${lineNo}: .align address overflows`);
        continue;
      }
      if (op === '.code' || op === '.data') {
        if (words.length !== 1) fail(`Line ${lineNo}: ${op} syntax is ${op} label`);
        if (op === '.code' && ((pc & 3) || pc + 4 > RAM_BYTES)) fail(`Line ${lineNo}: code label must be word-aligned in installed RAM`);
        defineLabel(words[0], pc, lineNo); continue;
      }
      if (op === '.str') {
        if (!/^"(?:[^"\\]|\\.)*"$/.test(rest.trim())) fail(`Line ${lineNo}: .str syntax is .str "US-ASCII text"`);
        let value;
        try { value = JSON.parse(rest.trim()); } catch { fail(`Line ${lineNo}: invalid .str quoting or escape`); }
        for (let i = 0; i < value.length; i++) {
          const byte = value.charCodeAt(i);
          if (byte > 0x7f) fail(`Line ${lineNo}: .str accepts US-ASCII characters only`);
          reserve(pc, 1, lineNo); dataImage.push({ address: pc++, value, byte, width: 1, lineNo });
        }
        continue;
      }
      if (['.u8','.u16','.u32'].includes(op)) {
        if (!words.length) fail(`Line ${lineNo}: ${op} requires at least one unsigned value`);
        const width = op === '.u8' ? 1 : op === '.u16' ? 2 : 4;
        for (const valueText of words) { reserve(pc, width, lineNo); dataImage.push({ address: pc, valueText, width, lineNo }); pc += width; }
        continue;
      }
      addInstruction(line, lineNo);
    }
    function evalData(text, address, lineNo) {
      const n = parseNum(text);
      if (n !== null) return n;
      const d = /^\(\s*\$\s*-\s*(:?[\w.$]+)\s*\)$/.exec(text);
      if (d) return address - labelValue(d[1], lineNo);
      return labelValue(text, lineNo);
    }
    for (const d of dataImage) {
      if (d.width === 1 && d.byte !== undefined) { d.value = d.byte; continue; }
      const value = evalData(d.valueText, d.address, d.lineNo), max = d.width === 1 ? 0xff : d.width === 2 ? 0xffff : 0xffffffff;
      if (!Number.isInteger(value) || value < 0 || value > max) fail(`Line ${d.lineNo}: ${d.valueText} does not fit in .${d.width === 1 ? 'u8' : d.width === 2 ? 'u16' : 'u32'}`);
      d.value = u32(value);
    }
    const code = raw.map(item => parseInstruction(item, labels));
    for (const ins of code) {
      ins.encoding = encodeInstruction(ins);
      if (ins.encoding.word === 0) fail(`Line ${ins.lineNo}: the all-zero instruction word is reserved`);
    }
    code.labels = labels; code.data = dataImage; code.startPC = entryPC === null ? 0 : entryPC;
    return code;
  }
  function parseImm(text, labels, pc, lineNo, mode = 'signed', allowLabel = false) {
    let value = parseNum(text);
    if (value === null && allowLabel && labels) {
      const key = pcLabel(text);
      if (labels.has(key)) value = labels.get(key) - pc;
    }
    if (value === null) fail(`Line ${lineNo}: expected a numeric immediate, got “${text}”`);
    return checked16(value, lineNo, mode);
  }
  function requireReg(text, lineNo) {
    const r = register(text);
    if (r === null) fail(`Line ${lineNo}: invalid register “${text}”`);
    return r;
  }
  function requireDataDest(text, lineNo) {
    const r = requireReg(text, lineNo);
    if (r === 13 || r === 14 || r === 15) fail(`Line ${lineNo}: data-processing destination must be R0–R12`);
    return r;
  }
  function requireFloat(text, lineNo) {
    const s = String(text).trim().toLowerCase();
    if (!/^f(?:9|1[0-2])$/.test(s)) fail(`Line ${lineNo}: floating-point operand must be F9–F12`);
    return Number(s.slice(1));
  }
  function resolveMemory(text, labels, pc, lineNo) {
    const regPat = '(r\\d+|cusr|sr|sp|pc)';
    const m = new RegExp(`^(.*?)\\(\\s*${regPat}\\s*\\)$`, 'i').exec(text.trim());
    if (m) {
      const base = requireReg(m[2], lineNo), expr = m[1].trim();
      if (!expr) return { base, offset: 0, knownAddress: base === 0 ? 0 : base === 15 ? pc : null };
      const n = parseNum(expr);
      if (n !== null) return { base, offset: checked16(n, lineNo), knownAddress: base === 0 ? u32(n) : base === 15 ? u32(pc + n) : null };
      const key = pcLabel(expr);
      if (!labels.has(key)) fail(`Line ${lineNo}: unknown memory label “${expr}”`);
      const address = labels.get(key), offset = base === 0 ? address : address - pc;
      return { base, offset: checked16(offset, lineNo), knownAddress: base === 0 || base === 15 ? address : null };
    }
    const indirect = /^\(\s*([^()]+)\s*\)$/.exec(text.trim());
    if (indirect) {
      const name = indirect[1].trim(), r = register(name);
      if (r !== null) return { base: r, offset: 0, knownAddress: r === 0 ? 0 : r === 15 ? pc : null };
      const key = pcLabel(name);
      if (!labels.has(key)) fail(`Line ${lineNo}: unknown memory label “${name}”`);
      const address = labels.get(key);
      return { base: 15, offset: checked16(address - pc, lineNo), knownAddress: address };
    }
    return null;
  }
  function validateKnownAlignment(mem, op, lineNo) {
    const alignment = ['ld','st'].includes(op) ? 4 : ['ldh','ldsh','sth'].includes(op) ? 2 : 1;
    if (mem.knownAddress !== null && mem.knownAddress !== undefined && mem.knownAddress % alignment)
      fail(`Line ${lineNo}: ${op.toUpperCase()} effective address must be ${alignment}-byte aligned`);
  }
  function parseInstruction(item, labels) {
    const { line, lineNo, pc } = item;
    const split = line.search(/\s/), original = (split < 0 ? line : line.slice(0, split)).toLowerCase();
    let op = original, args = split < 0 ? [] : splitArgs(line.slice(split).trim());
    if (args.some(a => !a)) fail(`Line ${lineNo}: empty operand`);
    const ins = { op, args, line, lineNo, pc, mode: 0, rd: 0, rs: 0, imm: 0 };
    const make = (kind, fields = {}) => Object.assign(ins, { kind }, fields);
    const label = (token) => labels.get(pcLabel(token));
    ins.op = op;

    if (Object.hasOwn(COND, op)) {
      if (args.length !== 1) fail(`Line ${lineNo}: ${original.toUpperCase()} takes one target`);
      const cond = COND[op], targetReg = register(args[0]);
      ins.op = 'b'; ins.rd = cond;
      if (targetReg !== null) { ins.rs = targetReg; ins.imm = 0; }
      else {
        const n = parseNum(args[0]);
        let displacement;
        if (n !== null) {
          if (n % 4) fail(`Line ${lineNo}: branch byte displacement must be a multiple of 4`);
          displacement = n / 4;
        } else {
          const address = label(args[0]);
          if (address === undefined) fail(`Line ${lineNo}: unknown branch label “${args[0]}”`);
          const delta = address - pc;
          if (delta % 4) fail(`Line ${lineNo}: branch target is not word-aligned`);
          displacement = delta / 4;
        }
        ins.rs = 15; ins.imm = checked16(displacement, lineNo);
      }
      return make('branch', { cond, link: cond === 14 });
    }
    if (op === 'swi') {
      if (args.length !== 1) fail(`Line ${lineNo}: SWI syntax is SWI imm`);
      const value = parseImm(args[0], null, pc, lineNo, 'unsigned');
      if (value > 63) fail(`Line ${lineNo}: SWI immediate must be 0–63`);
      ins.imm = value; return make('swi');
    }
    if (op === 'rts' || op === 'rti') {
      if (args.length) fail(`Line ${lineNo}: ${op.toUpperCase()} takes no operands`);
      return make(op);
    }
    if (op === 'push' || op === 'pop') {
      if (args.length !== 1) fail(`Line ${lineNo}: ${op.toUpperCase()} takes one register`);
      const r = requireReg(args[0], lineNo);
      if (op === 'push') { ins.rs = r; return make('push'); }
      ins.rd = r; return make('pop');
    }
    if (['ld','ldb','ldh','ldsb','ldsh'].includes(op)) {
      if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} Rd, operand`);
      const rd = requireReg(args[0], lineNo), source = args[1];
      if (op === 'ld' && rd === 14) {
        const rs = register(source);
        if (rs === null) fail(`Line ${lineNo}: LD SP, Rs requires a register`);
        ins.rd = 14; ins.rs = rs; return make('set-sp');
      }
      if (rd === 15 || rd === 14 || (rd === 13 && op !== 'ld')) fail(`Line ${lineNo}: ${op.toUpperCase()} destination must be R0–R12`);
      ins.rd = rd;
      if (op !== 'ld') {
        const mem = resolveMemory(source, labels, pc, lineNo);
        if (!mem) fail(`Line ${lineNo}: ${op.toUpperCase()} requires a memory operand`);
        validateKnownAlignment(mem, op, lineNo);
        ins.mode = 1; ins.rs = mem.base; ins.imm = mem.offset; return make('memory');
      }
      const mem = resolveMemory(source, labels, pc, lineNo);
      if (mem) {
        if (rd === 13) fail(`Line ${lineNo}: LD R13 only accepts a register source`);
        validateKnownAlignment(mem, op, lineNo);
        ins.mode = 1; ins.rs = mem.base; ins.imm = mem.offset; return make('memory');
      }
      const rs = register(source);
      if (rs !== null) { ins.rs = rs; return make('move'); }
      const n = parseNum(source);
      if (n !== null) {
        if (rd === 13) fail(`Line ${lineNo}: LD R13 only accepts a register source`);
        ins.imm = checked16(n, lineNo, 'unsigned'); return make('ld-imm');
      }
      const address = label(source);
      if (address !== undefined) {
        if (rd === 13) fail(`Line ${lineNo}: LD R13 only accepts a register source`);
        ins.rs = 15; ins.imm = checked16(address - pc, lineNo); return make('ld-address');
      }
      fail(`Line ${lineNo}: invalid LD operand “${source}”`);
    }
    if (op === 'st' || op === 'stb' || op === 'sth') {
      if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} memory, Rvalue`);
      const mem = resolveMemory(args[0], labels, pc, lineNo);
      if (!mem) fail(`Line ${lineNo}: ${op.toUpperCase()} requires a memory operand`);
      validateKnownAlignment(mem, op, lineNo);
      ins.mode = 1; ins.rs = mem.base; ins.imm = mem.offset; ins.rd = requireReg(args[1], lineNo);
      return make('memory');
    }
    if (op === 'ldu') {
      if (args.length !== 2) fail(`Line ${lineNo}: LDU syntax is LDU Rd, imm16`);
      ins.rd = requireDataDest(args[0], lineNo); ins.imm = parseImm(args[1], labels, pc, lineNo, 'unsigned');
      return make('ldu');
    }
    if (op === 'swph' || op === 'swpb') {
      if (args.length !== 1) fail(`Line ${lineNo}: ${op.toUpperCase()} takes Rd`);
      ins.rd = requireDataDest(args[0], lineNo); return make('simple');
    }
    if (op === 'neg' || op === 'not') {
      if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} Rd, Rs`);
      ins.rd = requireDataDest(args[0], lineNo); ins.rs = requireReg(args[1], lineNo); return make('unary');
    }
    if (['btst','bset','bclr','bchg'].includes(op)) {
      if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} Rd, bit`);
      ins.rd = requireDataDest(args[0], lineNo); ins.imm = parseImm(args[1], labels, pc, lineNo, 'unsigned');
      if (ins.imm > 31) fail(`Line ${lineNo}: bit index must be 0–31`);
      return make('bit');
    }
    if (op === 'getb' || op === 'putb') {
      if (args.length !== (op === 'getb' ? 2 : 3)) fail(`Line ${lineNo}: invalid ${op.toUpperCase()} operands`);
      ins.rd = requireDataDest(args[0], lineNo);
      if (op === 'putb') ins.rs = requireReg(args[1], lineNo);
      const idx = parseImm(args[op === 'getb' ? 1 : 2], labels, pc, lineNo, 'unsigned');
      if (idx > 3) fail(`Line ${lineNo}: byte index must be 0–3`);
      ins.imm = idx; return make('byte-register');
    }
    if (['cmp','add','sub','adc','sbc','mul','mulu','mulh','mulhu','div','divu','divq','divqu',
      'and','or','xor','rol','ror','shl','shr','asr'].includes(op)) return parseInteger(ins, args, labels);
    if (['fcmp','fadd','fsub','fmul','fdiv','fabs','fneg','ftoi','itof'].includes(op)) return parseFloat(ins, args);
    fail(`Line ${lineNo}: unsupported instruction “${original}”`);
  }
  function parseInteger(ins, args, labels) {
    const op = ins.op, lineNo = ins.lineNo;
    if (op === 'cmp') {
      if (args.length !== 2) fail(`Line ${lineNo}: CMP takes Rd and a register or immediate`);
      ins.rd = requireDataDest(args[0], lineNo);
      const r = register(args[1]);
      if (r !== null) ins.rs = r;
      else ins.imm = parseImm(args[1], labels, ins.pc, lineNo, 'signed', true);
      return Object.assign(ins, { kind: 'integer' });
    }
    if (op === 'neg' || op === 'not') return ins;
    const ternary = ['add','sub','adc','sbc','mul','mulu','div','divu','mulh','mulhu','divq','divqu'];
    const twoOnly = ['and','or','xor','rol','ror','shl','shr','asr'];
    if (args.length < 2 || args.length > (twoOnly.includes(op) ? 2 : 3))
      fail(`Line ${lineNo}: invalid ${op.toUpperCase()} operand count`);
    ins.rd = requireDataDest(args[0], lineNo);
    const isWideResult = ['mulh','mulhu','divq','divqu'].includes(op);
    if (isWideResult && args.length === 2) {
      ins.rs = requireReg(args[1], lineNo);
      if (['divq','divqu'].includes(op) && ins.rd === ins.rs) fail(`Line ${lineNo}: ${op.toUpperCase()} requires Rd != Rs`);
      return Object.assign(ins, { kind: 'integer' });
    }
    if (args.length === 2) {
      const r = register(args[1]);
      if (r !== null) ins.rs = r;
      else ins.imm = parseImm(args[1], labels, ins.pc, lineNo,
        ['and','or','xor','mulu','mulhu','divu','divqu'].includes(op) ? 'unsigned' : 'signed', !['and','or','xor','rol','ror','shl','shr','asr'].includes(op));
      if (['rol','ror','shl','shr','asr'].includes(op)) {
        if (r === null) { const count = parseNum(args[1]); if (!Number.isInteger(count) || count < 0 || count > 31) fail(`Line ${lineNo}: shift count must be 0–31`); ins.imm = count; }
      }
      return Object.assign(ins, { kind: 'integer' });
    }
    if (!ternary.includes(op)) fail(`Line ${lineNo}: ${op.toUpperCase()} does not accept three operands`);
    ins.rs = requireReg(args[1], lineNo);
    const signedness = ['mulu','mulhu','divu','divqu'].includes(op) ? 'unsigned' : 'signed';
    ins.imm = parseImm(args[2], labels, ins.pc, lineNo, signedness, true);
    if (['mul','mulu','mulh','mulhu','div','divu','divq','divqu'].includes(op) && ins.imm === 0)
      fail(`Line ${lineNo}: three-operand ${op.toUpperCase()} with an immediate of zero has no distinct encoding`);
    if (['mul','mulu','div','divu'].includes(op) && ins.rs === 0)
      fail(`Line ${lineNo}: three-operand ${op.toUpperCase()} with R0 as Rs has no distinct encoding`);
    if (['divq','divqu'].includes(op) && ins.rd === ins.rs) fail(`Line ${lineNo}: ${op.toUpperCase()} requires Rd != Rs`);
    return Object.assign(ins, { kind: 'integer' });
  }
  function parseFloat(ins, args) {
    const op = ins.op, lineNo = ins.lineNo;
    if (op === 'fcmp') {
      if (args.length !== 2) fail(`Line ${lineNo}: FCMP takes Fd, Fs`);
      ins.rd = requireFloat(args[0], lineNo); ins.rs = requireFloat(args[1], lineNo);
    } else if (op === 'ftoi') {
      if (args.length !== 2) fail(`Line ${lineNo}: FTOI takes Rd, Fs`);
      ins.rd = requireDataDest(args[0], lineNo); ins.rs = requireFloat(args[1], lineNo);
    } else if (op === 'itof') {
      if (args.length !== 2) fail(`Line ${lineNo}: ITOF takes Fd, Rs`);
      ins.rd = requireFloat(args[0], lineNo); ins.rs = requireReg(args[1], lineNo);
    } else {
      if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} takes Fd, Fs`);
      ins.rd = requireFloat(args[0], lineNo); ins.rs = requireFloat(args[1], lineNo);
    }
    return Object.assign(ins, { kind: 'float' });
  }
  function encodeInstruction(ins) {
    const opcode = OPCODE[ins.op];
    if (opcode === undefined) fail(`Line ${ins.lineNo}: no opcode assigned to ${ins.op}`);
    const mode = ins.mode || 0, rd = ins.rd || 0, rs = ins.rs || 0, low16 = ins.imm & 0xffff;
    const word = (((mode & 1) << 31) | ((opcode & 0x7f) << 24) | ((rd & 15) << 20) | ((rs & 15) << 16) | low16) >>> 0;
    return { word, opcode, mode, rd, rs, low16 };
  }

  function readReg(r) {
    if (r === 0) return 0;
    if (r === 13) return state.regs[13] & CUSR_MASK;
    if (r === 15) return state.pc >>> 0;
    return state.regs[r] >>> 0;
  }
  function writeCusr(value) {
    const old = state.regs[13] & CUSR_MASK;
    const control = supervisor() ? (value & (FLAG.T | FLAG.S | FLAG.I)) : (old & (FLAG.T | FLAG.S | FLAG.I));
    const next = control | (value & SR_MASK);
    state.regs[13] = next >>> 0;
    if (old !== next) state.changedRegs.add(13);
  }
  function writeDataReg(r, value) {
    value = u32(value);
    if (r === 0) return;
    if (r === 13) { writeCusr(value); return; }
    if (r === 14 || r === 15) fail('Illegal data-processing destination', 3);
    state.regs[r] = value; state.changedRegs.add(r);
  }
  function updateNZ(result) {
    let sr = flags() & ~(FLAG.N | FLAG.Z);
    result = u32(result);
    if (result === 0) sr |= FLAG.Z;
    if (result & 0x80000000) sr |= FLAG.N;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function updateNZCV(result, carry, overflow) {
    result = u32(result);
    let sr = 0;
    if (result & 0x80000000) sr |= FLAG.N;
    if (result === 0) sr |= FLAG.Z;
    if (carry) sr |= FLAG.C;
    if (overflow) sr |= FLAG.V;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function updateLogicFlags(result) {
    let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.C | FLAG.V);
    result = u32(result);
    if (result & 0x80000000) sr |= FLAG.N;
    if (result === 0) sr |= FLAG.Z;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function updateShiftFlags(result, carry) {
    let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.V);
    result = u32(result);
    if (result & 0x80000000) sr |= FLAG.N;
    if (result === 0) sr |= FLAG.Z;
    if (carry !== null) sr = carry ? sr | FLAG.C : sr & ~FLAG.C;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function setCompare(a, b) {
    const signedA = BigInt(sx(a)), signedB = BigInt(sx(b));
    const result = u32(a - b), overflow = signedA - signedB > 2147483647n || signedA - signedB < -2147483648n;
    updateNZCV(result, BigInt(a >>> 0) >= BigInt(b >>> 0), overflow);
  }
  function checkMemory(address, width, alignment) {
    address = u32(address);
    if (address % alignment) fail(`Alignment fault at ${fmt(address)}`, 6);
    const inRam = address < RAM_BYTES && address + width <= RAM_BYTES;
    const inScreen = address >= SCREEN_BASE && address + width <= SCREEN_BASE + SCREEN_BYTES;
    if (!inRam && !inScreen) fail(`Illegal data memory access at ${fmt(address)}`, 5);
    return address;
  }
  function loadMemory(address, width) {
    address = checkMemory(address, width, width === 4 ? 4 : width === 2 ? 2 : 1);
    const view = address < RAM_BYTES ? state.ram : state.framebuffer;
    const offset = address < RAM_BYTES ? address : address - SCREEN_BASE;
    if (width === 1) return view.getUint8(offset);
    if (width === 2) return view.getUint16(offset, false);
    return view.getUint32(offset, false);
  }
  function storeMemory(address, value, width) {
    address = checkMemory(address, width, width === 4 ? 4 : width === 2 ? 2 : 1);
    const view = address < RAM_BYTES ? state.ram : state.framebuffer;
    const offset = address < RAM_BYTES ? address : address - SCREEN_BASE;
    if (width === 1) view.setUint8(offset, value & 0xff);
    else if (width === 2) view.setUint16(offset, value & 0xffff, false);
    else view.setUint32(offset, u32(value), false);
    for (let i = 0; i < width; i++) state.changedMem.add(address + i);
  }
  function checkStackPointer(value) {
    value = u32(value);
    if ((value & 3) || value > RAM_BYTES) fail(`Stack fault: invalid SP ${fmt(value)}`, 1);
    return value;
  }
  function pushWord(value) {
    const sp = checkStackPointer(state.regs[14]);
    if (sp < 4) fail('Stack fault: stack underflow', 1);
    const next = sp - 4;
    state.ram.setUint32(next, u32(value), false);
    state.changedMem.add(next); state.regs[14] = next; state.changedRegs.add(14);
  }
  function stackPeek(address) {
    const sp = checkStackPointer(address);
    if (sp + 4 > RAM_BYTES) fail('Stack fault: stack underflow', 1);
    return state.ram.getUint32(sp, false);
  }
  function condition(cond) {
    const f = flags();
    switch (cond) {
      case 0: return !!(f & FLAG.Z); case 1: return !(f & FLAG.Z);
      case 2: return !!(f & FLAG.C); case 3: return !(f & FLAG.C);
      case 4: return !!(f & FLAG.N); case 5: return !(f & FLAG.N);
      case 6: return !!(f & FLAG.V); case 7: return !(f & FLAG.V);
      case 8: return !!(f & FLAG.C) && !(f & FLAG.Z);
      case 9: return !(f & FLAG.C) || !!(f & FLAG.Z);
      case 10: return !!(!!(f & FLAG.N) === !!(f & FLAG.V));
      case 11: return !!(!!(f & FLAG.N) !== !!(f & FLAG.V));
      case 12: return !(f & FLAG.Z) && !!(!!(f & FLAG.N) === !!(f & FLAG.V));
      case 13: return !!(f & FLAG.Z) || !!(!!(f & FLAG.N) !== !!(f & FLAG.V));
      case 14: case 15: return true;
      default: return false;
    }
  }

  function invalidDecoded(message) { fail(message || 'Invalid instruction encoding', 3); }
  function decode(word, pc, display) {
    const mode = word >>> 31, opcode = (word >>> 24) & 0x7f, rd = (word >>> 20) & 15, rs = (word >>> 16) & 15, imm = word & 0xffff;
    const op = OPCODE_NAME.get(opcode);
    if (!op || word === 0) invalidDecoded('Invalid or reserved instruction');
    const ins = { op, opcode, mode, rd, rs, imm, pc, line: display || `${op.toUpperCase()} (encoded)`, encoding: {
      word: u32(word), opcode, mode, rd, rs, low16: imm
    } };
    const unused = (fields, message = 'Nonzero unused instruction field') => { if (fields) invalidDecoded(message); };
    if (op === 'b') {
      if (mode) invalidDecoded('B is only valid in mode 0');
      ins.kind = 'branch'; ins.cond = rd; ins.link = rd === 14;
      if (rs !== 15 && imm !== 0) invalidDecoded('Register-target branch requires zero displacement');
      return ins;
    }
    if (mode === 1) {
      if (!['ld','st','ldb','ldh','ldsb','ldsh','stb','sth'].includes(op)) invalidDecoded('Opcode is not valid in memory mode');
      if (op.startsWith('st')) ins.kind = 'memory';
      else {
        if (rd >= 13) invalidDecoded('Illegal load destination');
        ins.kind = 'memory';
      }
      ins.width = ['ldb','ldsb','stb'].includes(op) ? 1 : ['ldh','ldsh','sth'].includes(op) ? 2 : 4;
      return ins;
    }
    if (mode !== 0) invalidDecoded('Reserved instruction mode');
    if (op === 'swi') {
      unused(rd || rs, 'SWI requires Rd=Rs=0');
      if (imm > 63) invalidDecoded('SWI immediate is out of range');
      ins.kind = 'swi'; return ins;
    }
    if (op === 'rts' || op === 'rti') {
      unused(rd || rs || imm); ins.kind = op; return ins;
    }
    if (op === 'push') {
      unused(rd || imm, 'PUSH requires Rd=0 and immediate=0'); ins.kind = op; return ins;
    }
    if (op === 'pop') {
      unused(rs || imm, 'POP requires Rs=0 and immediate=0');
      if ((rd === 14 || rd === 15) && !supervisor()) fail('POP SP/PC outside supervisor mode', 3);
      ins.kind = op; return ins;
    }
    if (op === 'ld') {
      if (rd === 15) invalidDecoded('LD may not write PC');
      if (rd === 14) {
        unused(imm, 'LD SP register form requires immediate=0');
        ins.kind = 'set-sp'; return ins;
      }
      if (rd === 13 && imm !== 0) invalidDecoded('LD R13 only accepts a register source');
      if (rs === 15) ins.kind = 'ld-address';
      else if (rs === 0) ins.kind = 'ld-imm';
      else { unused(imm, 'Register LD requires immediate=0'); ins.kind = 'move'; }
      return ins;
    }
    if (op === 'ldu') {
      unused(rs, 'LDU requires Rs=0');
      if (rd >= 13) invalidDecoded('Illegal LDU destination');
      ins.kind = 'ldu'; return ins;
    }
    if (op === 'cmp') {
      if (rd >= 13) invalidDecoded('Illegal CMP destination');
      if (rs !== 0) unused(imm, 'Register CMP requires immediate=0');
      ins.kind = 'integer'; return ins;
    }
    if (['add','sub','adc','sbc','mul','mulu','mulh','mulhu','div','divu','divq','divqu',
      'and','or','xor','rol','ror','shl','shr','asr'].includes(op)) {
      if (rd >= 13) invalidDecoded('Illegal data-processing destination');
      if (['and','or','xor','rol','ror','shl','shr','asr'].includes(op) && rs !== 0) unused(imm, 'Register form requires immediate=0');
      if (['divq','divqu'].includes(op) && rd === rs) invalidDecoded(`${op.toUpperCase()} requires Rd != Rs`);
      if (['rol','ror','shl','shr','asr'].includes(op) && rs === 0 && (imm & 0xffe0)) invalidDecoded('Shift immediate has nonzero unused bits');
      ins.kind = 'integer'; return ins;
    }
    if (op === 'neg' || op === 'not') {
      if (rd >= 13) invalidDecoded('Illegal unary destination');
      unused(imm, 'Unary instruction requires immediate=0'); ins.kind = 'unary'; return ins;
    }
    if (['btst','bset','bclr','bchg'].includes(op)) {
      if (rd >= 13) invalidDecoded('Illegal bit-operation destination');
      unused(rs, 'Bit instruction requires Rs=0');
      unused(imm & 0xffe0, 'Bit index has nonzero unused bits'); ins.kind = 'bit'; return ins;
    }
    if (op === 'swph' || op === 'swpb') {
      if (rd >= 13) invalidDecoded('Illegal swap destination');
      unused(rs || imm); ins.kind = 'simple'; return ins;
    }
    if (op === 'getb') {
      if (rd >= 13) invalidDecoded('Illegal GETB destination');
      unused(rs || (imm & 0xfffc), 'GETB uses only the low two immediate bits'); ins.kind = 'byte-register'; return ins;
    }
    if (op === 'putb') {
      if (rd >= 13) invalidDecoded('Illegal PUTB destination');
      unused(imm & 0xfffc, 'PUTB uses only the low two immediate bits'); ins.kind = 'byte-register'; return ins;
    }
    if (['fcmp','fadd','fsub','fmul','fdiv','fabs','fneg','ftoi','itof'].includes(op)) {
      unused(imm, 'Floating-point form requires immediate=0');
      if (op === 'ftoi') { if (rd >= 13 || rs < 9 || rs > 12) invalidDecoded('Invalid FTOI registers'); }
      else if (op === 'itof') { if (rd < 9 || rd > 12) invalidDecoded('Invalid ITOF registers'); }
      else if (op === 'fcmp') { if (rd < 9 || rd > 12 || rs < 9 || rs > 12) invalidDecoded('Invalid FCMP registers'); }
      else if (op === 'fadd' || op === 'fsub' || op === 'fmul' || op === 'fdiv') { if (rd < 9 || rd > 12 || rs < 9 || rs > 12) invalidDecoded(`Invalid ${op.toUpperCase()} registers`); }
      else if (rd < 9 || rd > 12 || rs < 9 || rs > 12) invalidDecoded(`Invalid ${op.toUpperCase()} registers`);
      ins.kind = 'float'; return ins;
    }
    invalidDecoded('Invalid opcode/mode combination');
  }

  function isSignalingNaN(bits) {
    const exponent = bits & 0x7f800000, fraction = bits & 0x007fffff;
    return exponent === 0x7f800000 && fraction !== 0 && (fraction & 0x00400000) === 0;
  }
  const floatView = new DataView(new ArrayBuffer(4));
  function bitsToFloat(bits) { floatView.setUint32(0, u32(bits), false); return floatView.getFloat32(0, false); }
  function floatToBits(value) { floatView.setFloat32(0, value, false); return floatView.getUint32(0, false); }
  function setFloatArithmeticFlags(bits, overflow) {
    let sr = 0;
    if (bits & 0x80000000) sr |= FLAG.N;
    if ((bits & 0x7fffffff) === 0) sr |= FLAG.Z;
    if (overflow) sr |= FLAG.V;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function setFloatNZClearV(bits) {
    let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.V);
    if (bits & 0x80000000) sr |= FLAG.N;
    if ((bits & 0x7fffffff) === 0) sr |= FLAG.Z;
    state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
    state.changedRegs.add(13);
  }
  function executeFloat(ins) {
    const { op, rd, rs } = ins;
    const aBits = readReg(rd), bBits = readReg(rs);
    if (op === 'itof') { writeDataReg(rd, floatToBits(sx(readReg(rs)))); return; }
    if (op === 'ftoi') {
      const f = bitsToFloat(bBits);
      if (!Number.isFinite(f) || f < -2147483648 || f >= 2147483648) fail('FTOI invalid or out of range', 7);
      const result = u32(Math.trunc(f));
      let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.V);
      if (result & 0x80000000) sr |= FLAG.N;
      if (result === 0) sr |= FLAG.Z;
      state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr; state.changedRegs.add(13);
      writeDataReg(rd, result);
      return;
    }
    if (op === 'fabs' || op === 'fneg') {
      const result = op === 'fabs' ? (bBits & 0x7fffffff) : (bBits ^ 0x80000000);
      setFloatNZClearV(result); writeDataReg(rd, result); return;
    }
    const a = bitsToFloat(aBits), b = bitsToFloat(bBits);
    if (op === 'fcmp') {
      if (Number.isNaN(a) || Number.isNaN(b)) fail('FCMP invalid comparison (NaN)', 7);
      let sr = 0;
      if (a < b) sr |= FLAG.N;
      if (a === b) sr |= FLAG.Z;
      if (a >= b) sr |= FLAG.C;
      state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
      state.changedRegs.add(13); return;
    }
    if (isSignalingNaN(aBits) || isSignalingNaN(bBits)) fail(`${op.toUpperCase()} signaling NaN`, 7);
    let result;
    if (op === 'fadd') result = a + b;
    else if (op === 'fsub') result = a - b;
    else if (op === 'fmul') result = a * b;
    else if (op === 'fdiv') result = a / b;
    else invalidDecoded(`Invalid floating-point operation ${op}`);
    const hasQuietNaN = (Number.isNaN(a) && !isSignalingNaN(aBits)) || (Number.isNaN(b) && !isSignalingNaN(bBits));
    if (Number.isNaN(result) && !hasQuietNaN) fail(`${op.toUpperCase()} invalid floating-point operation`, 7);
    const rounded = Math.fround(result), bits = floatToBits(rounded);
    const overflow = Number.isFinite(a) && Number.isFinite(b) && !Number.isFinite(rounded) && !(op === 'fdiv' && b === 0);
    setFloatArithmeticFlags(bits, overflow);
    writeDataReg(rd, bits);
  }

  function executeInteger(ins) {
    const { op, rd, rs, imm } = ins;
    const lhs = readReg(rd), regValue = readReg(rs), simm = sign16(imm), uimm = imm;
    if (op === 'cmp') { setCompare(lhs, rs === 0 ? u32(simm) : regValue); return; }
    if (op === 'neg' || op === 'not') {
      const src = regValue, result = op === 'neg' ? u32(-src) : u32(~src);
      if (op === 'neg') {
        const overflow = src === 0x80000000;
        updateNZCV(result, src === 0, overflow);
      } else updateLogicFlags(result);
      writeDataReg(rd, result); return;
    }
    if (['btst','bset','bclr','bchg'].includes(op)) {
      const bit = imm & 31, mask = (1 << bit) >>> 0;
      if (op === 'btst') {
        const set = !!(lhs & mask);
        let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.C | FLAG.V);
        if (!set) sr |= FLAG.Z;
        if (bit === 31 && set) sr |= FLAG.N;
        state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr;
        state.changedRegs.add(13); return;
      }
      let result = op === 'bset' ? (lhs | mask) : op === 'bclr' ? (lhs & ~mask) : (lhs ^ mask);
      result = u32(result); updateLogicFlags(result); writeDataReg(rd, result); return;
    }
    if (op === 'swph') { writeDataReg(rd, u32((lhs << 16) | (lhs >>> 16))); return; }
    if (op === 'swpb') {
      const result = (((lhs & 0xff) << 24) | ((lhs & 0xff00) << 8) | ((lhs >>> 8) & 0xff00) | (lhs >>> 24)) >>> 0;
      writeDataReg(rd, result); return;
    }
    if (op === 'getb') { writeDataReg(rd, (lhs >>> ((imm & 3) * 8)) & 0xff); return; }
    if (op === 'putb') {
      const shift = (imm & 3) * 8, mask = (0xff << shift) >>> 0;
      writeDataReg(rd, (lhs & ~mask) | ((regValue & 0xff) << shift)); return;
    }
    if (op === 'mul' || op === 'mulu') {
      const unsigned = op === 'mulu';
      const a = rs !== 0 && imm !== 0 ? regValue : lhs;
      const b = rs !== 0 && imm !== 0 ? (unsigned ? uimm : u32(simm)) : (rs !== 0 ? regValue : (unsigned ? uimm : u32(simm)));
      const product = unsigned ? BigInt(a) * BigInt(b) : BigInt(sx(a)) * BigInt(sx(b));
      const result = Number(BigInt.asUintN(32, product));
      const overflow = unsigned ? product > 0xffffffffn : product > 2147483647n || product < -2147483648n;
      updateNZ(result);
      let sr = flags(); sr = overflow ? sr | FLAG.V : sr & ~FLAG.V;
      state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr; state.changedRegs.add(13);
      writeDataReg(rd, result); return;
    }
    if (op === 'mulh' || op === 'mulhu') {
      const unsigned = op === 'mulhu';
      const a = imm !== 0 ? regValue : lhs;
      const b = imm !== 0 ? (unsigned ? uimm : u32(simm)) : regValue;
      const product = unsigned ? BigInt(a) * BigInt(b) : BigInt(sx(a)) * BigInt(sx(b));
      const result = Number(BigInt.asUintN(64, product) >> 32n) >>> 0;
      const overflow = unsigned ? result !== 0 : product > 2147483647n || product < -2147483648n;
      updateNZ(result);
      let sr = flags(); sr = overflow ? sr | FLAG.V : sr & ~FLAG.V;
      state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr; state.changedRegs.add(13);
      writeDataReg(rd, result); return;
    }
    if (op === 'div' || op === 'divu' || op === 'divq' || op === 'divqu') {
      const unsigned = op === 'divu' || op === 'divqu', withRemainder = op === 'divq' || op === 'divqu';
      let dividend, divisor, remainderDest = rs;
      if (withRemainder && imm !== 0) { dividend = lhs; divisor = unsigned ? uimm : simm; }
      else if ((op === 'div' || op === 'divu') && rs !== 0 && imm !== 0) { dividend = regValue; divisor = unsigned ? uimm : simm; }
      else { dividend = lhs; divisor = rs !== 0 ? regValue : (unsigned ? uimm : simm); }
      if ((unsigned ? u32(divisor) : divisor) === 0) fail('Division by zero', 2);
      let quotient, remainder, overflow = false;
      if (unsigned) {
        const a = BigInt(u32(dividend)), b = BigInt(u32(divisor));
        quotient = Number(a / b); remainder = Number(a % b);
      } else {
        const a = sx(dividend), b = sx(divisor);
        if (a === -2147483648 && b === -1) { quotient = -2147483648; remainder = 0; overflow = true; }
        else { quotient = Math.trunc(a / b); remainder = a % b; }
      }
      const result = u32(quotient);
      updateNZ(result);
      let sr = flags(); sr = overflow ? sr | FLAG.V : sr & ~FLAG.V;
      state.regs[13] = (state.regs[13] & (FLAG.T | FLAG.S | FLAG.I)) | sr; state.changedRegs.add(13);
      writeDataReg(rd, result);
      if (withRemainder) writeDataReg(remainderDest, u32(remainder));
      return;
    }
    if (op === 'and' || op === 'or' || op === 'xor') {
      const rhs = rs === 0 ? uimm : regValue;
      const result = op === 'and' ? lhs & rhs : op === 'or' ? lhs | rhs : lhs ^ rhs;
      updateLogicFlags(result); writeDataReg(rd, result); return;
    }
    if (['rol','ror','shl','shr','asr'].includes(op)) {
      const count = (rs === 0 ? imm : regValue) & 31;
      let result = lhs, carry = null;
      if (count) {
        if (op === 'shl') { result = u32(lhs << count); carry = !!((lhs >>> (32 - count)) & 1); }
        else if (op === 'shr') { result = lhs >>> count; carry = !!((lhs >>> (count - 1)) & 1); }
        else if (op === 'asr') { result = u32(sx(lhs) >> count); carry = !!((lhs >>> (count - 1)) & 1); }
        else if (op === 'rol') { result = u32((lhs << count) | (lhs >>> (32 - count))); carry = !!((lhs >>> (32 - count)) & 1); }
        else { result = u32((lhs >>> count) | (lhs << (32 - count))); carry = !!((lhs >>> (count - 1)) & 1); }
      }
      updateShiftFlags(result, carry); writeDataReg(rd, result); return;
    }
    if (op === 'add' || op === 'adc' || op === 'sub' || op === 'sbc') {
      const a = BigInt(lhs), b = BigInt(regValue), si = BigInt(simm), cin = op === 'adc' && (flags() & FLAG.C) ? 1n : 0n;
      const subtract = op === 'sub' || op === 'sbc';
      const signedA = BigInt(sx(lhs)), signedB = BigInt(sx(regValue));
      let result, carry, signedResult;
      if (!subtract) {
        const extra = op === 'adc' ? cin : 0n;
        const unsignedWide = a + b + BigInt(u32(simm)) + extra;
        signedResult = signedA + signedB + si + extra;
        result = Number(BigInt.asUintN(32, unsignedWide)); carry = unsignedWide > 0xffffffffn;
      } else {
        const borrow = op === 'sbc' && !(flags() & FLAG.C) ? 1n : 0n;
        const unsignedSubtrahend = b + BigInt(u32(simm)) + borrow;
        const unsignedDiff = a - unsignedSubtrahend;
        signedResult = signedA - signedB - si - borrow;
        result = Number(BigInt.asUintN(32, unsignedDiff)); carry = unsignedDiff >= 0n;
      }
      const overflow = signedResult > 2147483647n || signedResult < -2147483648n;
      updateNZCV(result, carry, overflow); writeDataReg(rd, result); return;
    }
    invalidDecoded(`Unsupported integer operation ${op}`);
  }

  function execute(ins, nextPC) {
    const { op, rd, rs, imm } = ins;
    if (ins.kind === 'swi') {
      if (imm === 0) { reset(state.program); return state.pc; }
      if (imm === 63) {
        state.halted = true; state.pc = u32(nextPC); state.regs[15] = state.pc; state.changedRegs.add(15);
        return nextPC;
      }
      if (imm >= 1 && imm <= 8) { enterException(imm, `SWI service ${imm} ROM handler unavailable`, nextPC); return state.pc; }
      fail('Reserved SWI number', 3);
    }
    if (ins.kind === 'branch') {
      if (!condition(ins.cond)) return nextPC;
      let target;
      if (rs === 15) {
        const n = state.pc + sign16(imm) * 4;
        if (n < 0 || n > 0xffffffff) fail('Program counter overflow', 4);
        target = n >>> 0;
      } else target = readReg(rs);
      if (target & 3) fail(`Misaligned branch target ${fmt(target)}`, 6);
      if (ins.link) pushWord(nextPC);
      return target;
    }
    if (ins.kind === 'push') { pushWord(readReg(rs)); return nextPC; }
    if (ins.kind === 'pop') {
      if ((rd === 14 || rd === 15) && !supervisor()) fail('POP SP/PC outside supervisor mode', 3);
      const oldSP = checkStackPointer(state.regs[14]), value = stackPeek(oldSP), incremented = oldSP + 4;
      if (incremented > RAM_BYTES) fail('Stack fault: stack underflow', 1);
      if (rd === 14) {
        const loadedSP = checkStackPointer(value);
        state.regs[14] = loadedSP; state.changedRegs.add(14);
      } else if (rd === 15) {
        if (value & 3) fail(`Misaligned POP PC target ${fmt(value)}`, 6);
        state.regs[14] = incremented; state.changedRegs.add(14); return value;
      } else {
        state.regs[14] = incremented; state.changedRegs.add(14);
        if (rd === 13) writeCusr(value); else writeDataReg(rd, value);
      }
      return nextPC;
    }
    if (ins.kind === 'rts') {
      const oldSP = checkStackPointer(state.regs[14]), value = stackPeek(oldSP), incremented = oldSP + 4;
      if (incremented > RAM_BYTES) fail('Stack fault: stack underflow', 1);
      if (value & 3) fail(`Misaligned return address ${fmt(value)}`, 6);
      state.regs[14] = incremented; state.changedRegs.add(14); return value;
    }
    if (ins.kind === 'rti') {
      if (!supervisor()) fail('RTI outside supervisor mode', 3);
      const oldSP = checkStackPointer(state.regs[14]);
      const savedCusr = stackPeek(oldSP), savedPC = stackPeek(oldSP + 4), newSP = oldSP + 8;
      if (newSP > RAM_BYTES) fail('Stack fault: stack underflow', 1);
      if (savedPC & 3) fail(`Misaligned RTI address ${fmt(savedPC)}`, 6);
      state.regs[14] = newSP; state.changedRegs.add(14);
      state.regs[13] = savedCusr & CUSR_MASK; state.changedRegs.add(13);
      return savedPC;
    }
    if (ins.kind === 'set-sp') {
      const sp = checkStackPointer(readReg(rs)); state.regs[14] = sp; state.changedRegs.add(14); return nextPC;
    }
    if (ins.kind === 'ld-imm') {
      const value = imm;
      if (rd === 13) writeCusr(value); else if (rd === 14) { const sp = checkStackPointer(value); state.regs[14] = sp; state.changedRegs.add(14); } else writeDataReg(rd, value);
      return nextPC;
    }
    if (ins.kind === 'ld-address') {
      const address = state.pc + sign16(imm);
      if (address < 0 || address > 0xffffffff) fail('Program counter overflow', 4);
      if (rd === 13) writeCusr(address); else writeDataReg(rd, address);
      return nextPC;
    }
    if (ins.kind === 'move') {
      const value = readReg(rs);
      if (rd === 13) writeCusr(value);
      else if (rd === 14) { const sp = checkStackPointer(value); state.regs[14] = sp; state.changedRegs.add(14); }
      else writeDataReg(rd, value);
      return nextPC;
    }
    if (ins.kind === 'ldu') {
      writeDataReg(rd, ((imm << 16) | (readReg(rd) & 0xffff)) >>> 0); return nextPC;
    }
    if (ins.kind === 'memory') {
      const address = u32(readReg(rs) + sign16(imm));
      if (op === 'st' || op === 'stb' || op === 'sth') storeMemory(address, readReg(rd), ins.width || (op === 'stb' ? 1 : op === 'sth' ? 2 : 4));
      else {
        let value = loadMemory(address, ins.width || (op === 'ldb' || op === 'ldsb' ? 1 : op === 'ldh' || op === 'ldsh' ? 2 : 4));
        if (op === 'ldsb' && (value & 0x80)) value |= 0xffffff00;
        if (op === 'ldsh' && (value & 0x8000)) value |= 0xffff0000;
        writeDataReg(rd, value);
      }
      return nextPC;
    }
    if (ins.kind === 'integer' || ins.kind === 'unary' || ins.kind === 'bit' || ins.kind === 'simple' || ins.kind === 'byte-register') {
      executeInteger(ins); return nextPC;
    }
    if (ins.kind === 'float') { executeFloat(ins); return nextPC; }
    invalidDecoded(`Unsupported instruction kind ${ins.kind}`);
  }

  function enterException(vector, message, savedPC) {
    try {
      pushWord(savedPC);
      pushWord(state.regs[13] & CUSR_MASK);
      state.regs[13] = ((state.regs[13] | FLAG.S) & ~FLAG.I) & CUSR_MASK;
      state.changedRegs.add(13);
      state.trap = `${message} (vector ${vector}; ROM handler unavailable in this POC)`;
      state.halted = true;
    } catch (e) {
      state.regs[13] = (state.regs[13] | FLAG.T) & CUSR_MASK;
      state.trap = `Exception entry failed: ${e.message}`;
      state.halted = true;
      state.changedRegs.add(13);
    }
  }
  function storeInitialized(address, value, width) {
    for (let i = 0; i < width; i++) {
      const at = address + i, byte = (value >>> ((width - i - 1) * 8)) & 0xff;
      if (at >= 0 && at < RAM_BYTES) state.ram.setUint8(at, byte);
      else if (at >= SCREEN_BASE && at < SCREEN_BASE + SCREEN_BYTES) state.framebuffer.setUint8(at - SCREEN_BASE, byte);
      else fail(`Invalid initialized data address ${fmt(at)}`, 5);
      state.changedMem.add(at);
    }
  }
  function reset(instructions = []) {
    state.regs.fill(0); state.pc = instructions.startPC ?? 0; state.cycles = 0;
    state.ram = new DataView(new ArrayBuffer(RAM_BYTES));
    state.framebuffer = new DataView(new ArrayBuffer(SCREEN_BYTES));
    state.program = instructions; state.sourceMap = new Map(instructions.map(i => [i.pc, i]));
    state.dataImage = instructions.data || [];
    state.halted = false; state.trap = null; state.changedRegs.clear(); state.changedMem.clear(); state.last = null;
    state.regs[13] = FLAG.S; // POC reset shim: ROM boot code selects the assembled entry point.
    state.regs[14] = RAM_BYTES; state.regs[15] = state.pc;
    for (const ins of instructions) {
      if (ins.pc < 0 || ins.pc + 4 > RAM_BYTES || (ins.pc & 3)) fail(`Invalid instruction address ${fmt(ins.pc)}`, 5);
      state.ram.setUint32(ins.pc, ins.encoding.word, false);
    }
    for (const d of state.dataImage) storeInitialized(d.address, d.value, d.width);
    state.changedRegs.clear(); state.changedMem.clear();
  }
  function fetchWord(address) {
    address = u32(address);
    if (address & 3) fail(`Instruction alignment fault at ${fmt(address)}`, 6);
    if (address < RAM_BYTES && address + 4 <= RAM_BYTES) return state.ram.getUint32(address, false);
    if (address >= ROM_BASE && address + 4 <= ROM_BASE + ROM_BYTES)
      fail(`ROM instruction fetch at ${fmt(address)} unavailable in this POC`, 5);
    fail(`Instruction fetch outside installed memory at ${fmt(address)}`, 5);
  }
  function step() {
    if (state.halted) return null;
    const oldPC = state.pc >>> 0;
    let ins;
    state.changedRegs.clear(); state.changedMem.clear(); state.last = null;
    const oldCusr = state.regs[13];
    try {
      const word = fetchWord(oldPC), metadata = state.sourceMap.get(oldPC);
      ins = decode(word, oldPC, metadata && metadata.line);
      state.last = ins;
      if (oldPC > 0xfffffffb) fail('Program counter overflow', 4);
      const nextPC = oldPC + 4;
      state.cycles++;
      const target = execute(ins, nextPC);
      if (!state.halted && !state.trap) {
        state.pc = u32(target); state.regs[15] = state.pc; state.changedRegs.add(15);
      } else if (state.pc !== oldPC) {
        state.regs[15] = state.pc; state.changedRegs.add(15);
      }
      if (state.regs[13] !== oldCusr) state.changedRegs.add(13);
      return ins;
    } catch (e) {
      enterException(e.vector || 3, e.message, oldPC);
      return ins || null;
    }
  }
  function peekWord(address) { return loadMemory(address, 4); }

  return { state, assemble, reset, step, fmt, parseNum, peekWord, constants: { RAM_BYTES, SCREEN_BASE, SCREEN_BYTES, FLAG } };
})();
// Browser UI, intentionally separate from the CPU core above.
const $ = id => document.getElementById(id), cpu = TDC32.state;
let timer = null, fastRunning = false, fastChannel = null, fastDisabled = [];
let bitmapRendered = false, loadedSource = null, programFilename = 'tdc32-program.asm';
function valueDisplay(value) {
  const n = Number(value) >>> 0;
  return `<span class="hover-value" tabindex="0"><span class="value-main">${TDC32.fmt(n)}</span><span class="value-pop"><b>Hex:</b> ${TDC32.fmt(n)}<br><b>Dec:</b> ${n}<br><b>Bin:</b> ${n.toString(2).padStart(32, '0')}</span></span>`;
}
function flagUI() {
  const f = cpu.regs[13] >>> 0;
  const bits = [['T',0x8000],['S',0x4000],['I',0x2000],['V',8],['C',4],['N',2],['Z',1]];
  $('flags').innerHTML = bits.map(([name, bit]) => `<span class="flag ${f & bit ? 'on' : ''}">${name}</span>`).join('');
}
function render() {
  $('cycles').textContent = cpu.cycles;
  $('pc').innerHTML = valueDisplay(cpu.pc);
  $('sp').innerHTML = valueDisplay(cpu.regs[14]);
  $('cusr').innerHTML = valueDisplay(cpu.regs[13]);
  $('pc').className = cpu.changedRegs.has(15) ? 'changed' : '';
  $('sp').className = cpu.changedRegs.has(14) ? 'changed' : '';
  $('cusr').className = cpu.changedRegs.has(13) ? 'changed' : '';
  $('runstate').textContent = cpu.trap ? 'ROM / TRAP STOP' : cpu.halted ? 'Halted' : timer || fastRunning ? 'Running' : 'Ready';
  flagUI();
  $('registers').innerHTML = Array.from({ length: 13 }, (_, i) =>
    `<div class="reg ${cpu.changedRegs.has(i) ? 'changed' : ''}"><span>R${i}</span>${valueDisplay(cpu.regs[i])}</div>`
  ).join('');
  const ins = cpu.sourceMap.get(cpu.pc);
  $('current').textContent = cpu.trap ? cpu.trap : ins ? `${TDC32.fmt(ins.pc)}  ${ins.line}` : cpu.halted ? 'CPU halted' : 'No instruction at PC';
  renderMemory();
  renderBitmap();
}
function renderBitmap(force = false) {
  const width = 640, height = 480;
  if (!force && bitmapRendered && cpu.changedMem.size === 0) return;
  const canvas = $('bitmap'), ctx = canvas.getContext && canvas.getContext('2d');
  if (!ctx) return;
  const image = ctx.createImageData(width, height), pixels = image.data;
  let byte = 0;
  for (let p = 0; p < width * height; p++) {
    const bit = p & 7;
    if (bit === 0) byte = cpu.framebuffer.getUint8(p >>> 3);
    const on = (byte & (1 << (7 - bit))) !== 0, i = p * 4;
    pixels[i] = pixels[i + 1] = pixels[i + 2] = on ? 255 : 0;
    pixels[i + 3] = 255;
  }
  ctx.putImageData(image, 0, 0);
  bitmapRendered = true;
  $('bitmapInfo').textContent = `Packed monochrome, 1 bit/pixel, MSB first · base ${TDC32.fmt(TDC32.constants.SCREEN_BASE)}, ${TDC32.constants.SCREEN_BYTES} bytes.`;
}
function renderMemory() {
  let base = TDC32.parseNum($('memaddr').value.trim());
  if (base === null) base = 0;
  base = (base >>> 0) & ~3;
  const windowBytes = 64;
  const inRam = base >= 0 && base + windowBytes <= TDC32.constants.RAM_BYTES;
  const inScreen = base >= TDC32.constants.SCREEN_BASE && base + windowBytes <= TDC32.constants.SCREEN_BASE + TDC32.constants.SCREEN_BYTES;
  if (!inRam && !inScreen) base = 0;
  $('memaddr').value = TDC32.fmt(base);
  let html = '<div class="memrow head"><span>Address</span><span>+0</span><span>+4</span><span>+8</span><span>+C</span></div>';
  for (let row = 0; row < 4; row++) {
    const at = base + row * 16;
    html += `<div class="memrow"><span>${TDC32.fmt(at)}</span>`;
    for (let col = 0; col < 4; col++) {
      const addr = at + col * 4, val = TDC32.peekWord(addr);
      html += `<span class="${cpu.changedMem.has(addr) ? 'changed' : ''}">${TDC32.fmt(val)}</span>`;
    }
    html += '</div>';
  }
  $('memory').innerHTML = html;
}
function traceBatch(instructions) {
  const recent = instructions.slice(-160), fragment = document.createDocumentFragment();
  for (let i = recent.length - 1; i >= 0; i--) {
    const ins = recent[i], div = document.createElement('div'), enc = ins.encoding;
    const lowBits = enc.low16.toString(2).padStart(16, '0').replace(/(.{4})(?=.)/g, '$1_');
    const line = ins.line.replace(/[&<>]/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' })[ch]);
    div.innerHTML = `<span class="pc">${TDC32.fmt(ins.pc)}</span> &nbsp;${line}<span class="encoding"> &nbsp;<span class="word">${TDC32.fmt(enc.word)}</span> MODE:${enc.mode} opcode:${enc.opcode.toString(2).padStart(7, '0')} RD:${enc.rd.toString(2).padStart(4, '0')} RS:${enc.rs.toString(2).padStart(4, '0')} [15:0]:${lowBits}</span>`;
    fragment.appendChild(div);
  }
  $('trace').prepend(fragment);
  while ($('trace').children.length > 160) $('trace').lastChild.remove();
}
function trace(ins) { traceBatch([ins]); }
function setFastUI(disabled) {
  if (disabled) {
    fastDisabled = Array.from(document.querySelectorAll('button, textarea, input, select'))
      .filter(el => el.id !== 'stop').map(el => [el, el.disabled]);
    fastDisabled.forEach(([el]) => { el.disabled = true; });
  } else {
    fastDisabled.forEach(([el, wasDisabled]) => { el.disabled = wasDisabled; });
    fastDisabled = [];
  }
}
function stop() {
  if (timer) { clearInterval(timer); timer = null; }
  if (fastRunning) {
    fastRunning = false;
    if (fastChannel) { fastChannel.port1.close(); fastChannel.port2.close(); fastChannel = null; }
    setFastUI(false);
  }
  render();
}
function runFastChunk() {
  if (!fastRunning) return;
  const batch = []; let memoryChanged = false;
  for (let i = 0; i < 512 && !cpu.halted && !cpu.trap; i++) {
    const ins = TDC32.step();
    if (ins) batch.push(ins);
    if (cpu.changedMem.size) memoryChanged = true;
    if (!ins) break;
  }
  if (memoryChanged) bitmapRendered = false;
  traceBatch(batch); render();
  if (cpu.halted || cpu.trap) { stop(); return; }
  if (fastRunning && fastChannel) fastChannel.port2.postMessage(0);
}
function startFastRun() {
  fastRunning = true; setFastUI(true);
  fastChannel = new MessageChannel();
  fastChannel.port1.onmessage = runFastChunk;
  fastChannel.port2.postMessage(0);
  render();
}
function execute() {
  const ins = TDC32.step(); if (ins) trace(ins); render();
  if (cpu.halted || cpu.trap) stop();
}
$('reset').onclick = () => {
  stop();
  try {
    const code = TDC32.assemble($('source').value);
    TDC32.reset(code); loadedSource = $('source').value; bitmapRendered = false; $('trace').innerHTML = '';
    $('message').className = 'message';
    $('message').textContent = `Loaded ${code.length} instruction${code.length === 1 ? '' : 's'}; entry PC ${TDC32.fmt(code.startPC)}.`;
    render();
  } catch (e) { $('message').className = 'message error'; $('message').textContent = e.message; }
};
$('loadFile').onclick = () => $('programFile').click();
$('programFile').addEventListener('change', async event => {
  const file = event.target.files && event.target.files[0];
  if (!file) return;
  try {
    $('source').value = await file.text();
    programFilename = file.name || 'tdc32-program.asm';
    loadedSource = null; $('trace').innerHTML = '';
    $('message').className = 'message';
    $('message').textContent = `Loaded ${programFilename}; Step or Run to assemble and execute.`;
  } catch (e) {
    $('message').className = 'message error'; $('message').textContent = `Could not load file: ${e.message}`;
  }
  event.target.value = '';
});
$('saveFile').onclick = () => {
  const blob = new Blob([$('source').value], { type: 'text/plain;charset=utf-8' });
  const url = URL.createObjectURL(blob), link = document.createElement('a');
  link.href = url; link.download = programFilename; document.body.appendChild(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
  $('message').className = 'message'; $('message').textContent = `Saved ${programFilename}.`;
};
$('step').onclick = () => {
  if (!cpu.program.length || loadedSource !== $('source').value) $('reset').click();
  if (loadedSource !== $('source').value) return;
  if (!cpu.halted) execute();
};
$('run').onclick = () => {
  if (!cpu.program.length || loadedSource !== $('source').value) $('reset').click();
  if (loadedSource !== $('source').value || cpu.halted) return;
  stop();
  const interval = Number($('runDelay').value);
  if (interval === 0) startFastRun();
  else { timer = setInterval(execute, interval || 5); render(); }
};
$('stop').onclick = stop;
$('memrefresh').onclick = renderMemory;
$('memaddr').addEventListener('keydown', e => { if (e.key === 'Enter') renderMemory(); });
render();
