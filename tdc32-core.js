// TDC32.01 architectural POC. CPU core is isolated from the browser UI below.
'use strict';

const TDC32 = (() => {
  // POC installs 32 KiB of RAM at 0x0000; ROM vectors begin at 0x8000.
  // The debugger adds a 640x480, packed 1bpp video-memory device at 0x00010000.
  const RAM_BYTES = 0x8000, SCREEN_BASE = 0x00010000, SCREEN_BYTES = 640 * 480 / 8;
  const FLAG = { Z: 1, N: 2, C: 4, V: 8, I: 0x20, S: 0x4000, T: 0x8000 };
  const SR_MASK = FLAG.Z | FLAG.N | FLAG.C | FLAG.V | FLAG.I;
  const conds = {
    beq: 0, bne: 1, bcs: 2, bhs: 2, bcc: 3, blo: 3, bmi: 4, bpl: 5,
    bvs: 6, bvc: 7, bhi: 8, bls: 9, bge: 10, blt: 11, bgt: 12,
    ble: 13, ba: 15, b: 15
  };
  const state = {
    regs: new Uint32Array(16), pc: 0, cycles: 0,
    ram: new DataView(new ArrayBuffer(RAM_BYTES)),
    framebuffer: new DataView(new ArrayBuffer(SCREEN_BYTES)),
    program: [], sourceMap: new Map(), dataImage: [],
    halted: false, trap: null, changedRegs: new Set(), changedMem: new Set(),
    last: null
  };
  const u32 = n => Number(n) >>> 0;
  const sx = n => n | 0;
  const fmt = n => '0x' + u32(n).toString(16).toUpperCase().padStart(8, '0');
  const sign16 = n => (n << 16) >> 16;
  const flags = () => state.regs[13] & 0xff;
  const supervisor = () => !!(state.regs[13] & FLAG.S);
  const pcLabel = s => s.trim().replace(/^:/, '').toLowerCase();
  function fail(message, vector = 3) { const e = new Error(message); e.vector = vector; throw e; }

  function parseNum(text) {
    const s = String(text).replaceAll('_', '');
    if (/^[+-]?\d+$/.test(s)) return Number(s);
    if (/^\$[\da-f]+$/i.test(s)) return Number('0x' + s.slice(1));
    if (/^0x[\da-f]+$/i.test(s)) return Number(s);
    if (/^%[01]+$/.test(s)) return Number('0b' + s.slice(1));
    if (/^0b[01]+$/i.test(s)) return Number(s);
    return null;
  }

  function register(text) {
    const s = text.trim().toLowerCase();
    if (s === 'cusr' || s === 'sr') return 13;
    if (s === 'sp') return 14;
    if (s === 'pc') return 15;
    if (/^f(?:9|1[0-2])$/.test(s)) return Number(s.slice(1));
    const m = /^r(\d+)$/.exec(s);
    if (!m) return null;
    const n = Number(m[1]);
    return n >= 0 && n <= 15 ? n : null;
  }

  function splitArgs(s) { return s.split(',').map(x => x.trim()).filter(Boolean); }
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
  function literal32(s, lineNo) {
    const n = parseNum(s);
    if (n === null || !Number.isInteger(n) || n < -0x80000000 || n > 0xffffffff)
      fail(`Line ${lineNo}: expected a 32-bit literal for LI`);
    return u32(n);
  }

  // Assemble code and initialized data into their declared addresses.
  function assemble(source) {
    const labels = new Map(), raw = [], dataImage = [], occupiedBytes = new Set();
    let pc = 0, entryPC = null;
    const mappedByte = address => (address >= 0 && address < RAM_BYTES) ||
      (address >= SCREEN_BASE && address < SCREEN_BASE + SCREEN_BYTES);
    const reserve = (address, width, lineNo) => {
      if (!Number.isInteger(address) || address < 0 || address + width - 1 > 0xffffffff)
        fail(`Line ${lineNo}: invalid data address`);
      for (let i = 0; i < width; i++) {
        const at = address + i;
        if (!mappedByte(at)) fail(`Line ${lineNo}: data address ${fmt(at)} is not mapped`);
        if (occupiedBytes.has(at)) fail(`Line ${lineNo}: address ${fmt(at)} is already occupied`);
      }
      for (let i = 0; i < width; i++) occupiedBytes.add(address + i);
    };
    const defineLabel = (name, address, lineNo) => {
      if (!/^[\w.$]+$/.test(name)) fail(`Line ${lineNo}: invalid label “${name}”`);
      const key = name.toLowerCase();
      if (labels.has(key)) fail(`Line ${lineNo}: duplicate label ${name}`);
      labels.set(key, address);
    };
    const parseAddress = (text, lineNo, aligned = false) => {
      const address = parseNum(text);
      if (!Number.isInteger(address) || address < 0 || address > 0xffffffff || (aligned && (address & 3)))
        fail(`Line ${lineNo}: expected a ${aligned ? 'word-aligned ' : ''}32-bit address`);
      return address;
    };
    const dataArgs = text => text.split(/[\s,]+/).map(x => x.trim()).filter(Boolean);

    for (const [i, original] of source.split(/\r?\n/).entries()) {
      const lineNo = i + 1, line = cleanLine(original);
      if (!line) continue;
      const lm = /^:([\w.$]+)$/.exec(line);
      if (lm) { defineLabel(lm[1], pc, lineNo); continue; }
      const firstSpace = line.search(/\s/), mn = firstSpace < 0 ? line : line.slice(0, firstSpace);
      const op = mn.toLowerCase(), rest = firstSpace < 0 ? '' : line.slice(firstSpace).trimStart();
      const args = splitArgs(rest), words = dataArgs(rest);

      if (op === '.adr') {
        if (words.length !== 1) fail(`Line ${lineNo}: .adr syntax is .adr address`);
        pc = parseAddress(words[0], lineNo, true); continue;
      }
      if (op === '.code') {
        if (words.length !== 1) fail(`Line ${lineNo}: .code syntax is .code label`);
        if (pc + 4 > RAM_BYTES || (pc & 3)) fail(`Line ${lineNo}: code label must be word-aligned in installed RAM`);
        defineLabel(words[0], pc, lineNo); continue;
      }
      if (op === '.data') {
        if (words.length !== 1) fail(`Line ${lineNo}: .data syntax is .data name`);
        defineLabel(words[0], pc, lineNo); continue;
      }
      if (op === '.str') {
        const encoded = /^"(?:[^"\\]|\\.)*"$/.test(rest.trim());
        if (!encoded) fail(`Line ${lineNo}: .str syntax is .str "US-ASCII text"`);
        let text;
        try { text = JSON.parse(rest.trim()); } catch { fail(`Line ${lineNo}: invalid .str quoting or escape`); }
        for (let i = 0; i < text.length; i++) {
          const value = text.charCodeAt(i);
          if (value > 0x7f) fail(`Line ${lineNo}: .str accepts US-ASCII characters only`);
          reserve(pc, 1, lineNo); dataImage.push({ address: pc, valueText: String(value), width: 1, lineNo }); pc++;
        }
        continue;
      }
      if (['.u8','.u16','.u32'].includes(op)) {
        if (!words.length) fail(`Line ${lineNo}: ${op} requires at least one unsigned value`);
        const width = op === '.u8' ? 1 : op === '.u16' ? 2 : 4;
        for (const valueText of words) {
          reserve(pc, width, lineNo);
          dataImage.push({ address: pc, valueText, width, lineNo });
          pc += width;
        }
        continue;
      }
      if (op === 'min' || op === 'max') {
        if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} Rd, Rs`);
        const rd = register(args[0]), rs = register(args[1]);
        if (rd === null || rd > 12 || rs === null || rs > 12) fail(`Line ${lineNo}: ${op.toUpperCase()} operands must be R0–R12`);
        const keep = op === 'min' ? 'ble 2' : 'bge 2';
        const emitted = [`bpr ${args[0]}, ${args[1]}`, keep, `ld ${args[0]}, ${args[1]}`];
        for (const expanded of emitted) {
          if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
          reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
          if (entryPC === null) entryPC = pc;
          pc += 4;
        }
      } else if (op === 'abs') {
        if (args.length !== 2) fail(`Line ${lineNo}: ABS syntax is ABS Rd, Rs`);
        const rd = register(args[0]), rs = register(args[1]);
        if (rd === null || rd > 12 || rs === null || rs > 12) fail(`Line ${lineNo}: ABS operands must be R0–R12`);
        const target = rd === 0 ? 'r12' : args[0];
        const emitted = [`bpr ${args[1]}, 0`, 'bmi 4', `ld ${target}, ${args[1]}`, `bpr ${target}, 0`, 'ba 2', `sub ${target}, r0, ${args[1]}`];
        for (const expanded of emitted) {
          if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
          reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
          if (entryPC === null) entryPC = pc;
          pc += 4;
        }
      } else if (['btst','bset','bclr','bchg'].includes(op)) {
        if (args.length !== 2) fail(`Line ${lineNo}: ${op.toUpperCase()} syntax is ${op.toUpperCase()} Rd, bit`);
        const rd = register(args[0]), bit = parseNum(args[1]);
        if (rd === null || rd > 11) fail(`Line ${lineNo}: bit-operation target must be R0–R11; R12 is the alias scratch register`);
        if (!Number.isInteger(bit) || bit < 0 || bit > 31) fail(`Line ${lineNo}: bit index must be an integer from 0 to 31`);
        const mask = (2 ** bit) >>> 0, value = op === 'bclr' ? u32(~mask) : mask;
        const load = value <= 0xffff ? [`ld r12, ${value}`] : [`ld r12, ${value >>> 16}`, `ld.l r12, ${value & 0xffff}`];
        const logical = op === 'btst' ? `and r0, ${args[0]}, r12`
          : op === 'bset' ? `or ${args[0]}, ${args[0]}, r12`
          : op === 'bclr' ? `and ${args[0]}, ${args[0]}, r12`
          : `xor ${args[0]}, ${args[0]}, r12`;
        for (const expanded of [...load, logical]) {
          if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
          reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
          if (entryPC === null) entryPC = pc;
          pc += 4;
        }
      } else if (['neg','not','inc','dec'].includes(op)) {
        const unary = op === 'inc' || op === 'dec';
        if (args.length !== (unary ? 1 : 2)) fail(`Line ${lineNo}: invalid ${op.toUpperCase()} operands`);
        const rd = register(args[0]);
        if (rd === null || rd > (op === 'not' ? 11 : 13)) fail(`Line ${lineNo}: invalid ${op.toUpperCase()} destination`);
        if (op === 'not') {
          const rs = register(args[1]);
          if (rs === null || rs > 11) fail(`Line ${lineNo}: NOT source must be R0–R11; R12 is its scratch register`);
          const emitted = [`ld r12, 65535`, `ld.l r12, 65535`, `xor ${args[0]}, ${args[1]}, r12`];
          for (const expanded of emitted) {
            if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
            reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
            if (entryPC === null) entryPC = pc;
            pc += 4;
          }
        } else {
          let expanded;
          if (op === 'inc') expanded = `add ${args[0]}, ${args[0]}, 1`;
          else if (op === 'dec') expanded = `sub ${args[0]}, ${args[0]}, 1`;
          else {
            const rs = register(args[1]);
            if (rs === null) fail(`Line ${lineNo}: NEG source must be a register`);
            expanded = `sub ${args[0]}, r0, ${args[1]}`;
          }
          if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
          reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
          if (entryPC === null) entryPC = pc;
          pc += 4;
        }
      } else if (op === 'lea') {
        if (args.length !== 2) fail(`Line ${lineNo}: LEA syntax is LEA Rd, label`);
        const rd = register(args[0]);
        if (rd === null || rd > 13) fail(`Line ${lineNo}: LEA destination must be R0–R13`);
        if (parseNum(args[1]) !== null) fail(`Line ${lineNo}: LEA requires a label, not an immediate`);
        const expanded = `add ${args[0]}, pc, ${args[1]}`;
        if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
        reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, leaTarget: args[1], lineNo, pc });
        if (entryPC === null) entryPC = pc;
        pc += 4;
      } else if (op === 'li') {
        if (args.length !== 2) fail(`Line ${lineNo}: LI syntax is LI Rd, imm32`);
        const rd = register(args[0]);
        if (rd === null || rd > 13) fail(`Line ${lineNo}: LI destination must be R0–R13`);
        const value = literal32(args[1], lineNo), hi = value >>> 16, lo = value & 0xffff;
        const emitted = value <= 0xffff ? [`ld ${args[0]}, ${value}`] : [`ld ${args[0]}, ${hi}`, `ld.l ${args[0]}, ${lo}`];
        for (const expanded of emitted) {
          if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
          reserve(pc, 4, lineNo); raw.push({ line: expanded, displayLine: expanded, lineNo, pc });
          if (entryPC === null) entryPC = pc;
          pc += 4;
        }
      } else {
        if (pc & 3 || pc + 4 > RAM_BYTES) fail(`Line ${lineNo}: code must be assembled at an aligned address in installed RAM`);
        reserve(pc, 4, lineNo); raw.push({ line, displayLine: line, lineNo, pc });
        if (entryPC === null) entryPC = pc;
        pc += 4;
      }
    }

    for (const item of raw) {
      if (item.leaTarget && !labels.has(pcLabel(item.leaTarget)))
        fail(`Line ${item.lineNo}: unknown LEA label “${item.leaTarget}”`);
    }
    for (const data of dataImage) {
      let value = parseNum(data.valueText);
      if (value === null && labels.has(pcLabel(data.valueText))) value = labels.get(pcLabel(data.valueText));
      const limits = data.width === 1 ? 0xff : data.width === 2 ? 0xffff : 0xffffffff;
      if (!Number.isInteger(value) || value < 0 || value > limits)
        fail(`Line ${data.lineNo}: ${data.valueText} does not fit in .${data.width === 1 ? 'u8' : data.width === 2 ? 'u16' : 'u32'}`);
      data.value = u32(value);
    }
    const code = raw.map(item => parseInstruction(item, labels));
    code.labels = labels;
    code.data = dataImage;
    code.startPC = entryPC === null ? 0 : entryPC;
    return code;
  }

  function resolveImmediate(text, labels, pc, lineNo, allowLabel = true) {
    const n = parseNum(text);
    if (n !== null) return n;
    const key = pcLabel(text);
    if (allowLabel && labels.has(key)) return labels.get(key) - pc;
    fail(`Line ${lineNo}: unknown literal or label “${text}”`);
  }
  function checked16(n, lineNo, mode = 'signed') {
    const valid = mode === 'unsigned' ? Number.isInteger(n) && n >= 0 && n <= 0xffff
      : Number.isInteger(n) && n >= -0x8000 && n <= 0x7fff;
    if (!valid) fail(`Line ${lineNo}: immediate is outside the ${mode} 16-bit range`);
    return n;
  }
  function parseMemory(text, labels, pc, lineNo) {
    const m = /^(.*?)\((r\d+|cusr|sr|sp|pc|f(?:9|1[0-2]))\)$/i.exec(text.trim());
    if (!m) return null;
    const base = register(m[2]);
    let offset = 0;
    if (m[1].trim()) offset = resolveImmediate(m[1], labels, pc, lineNo);
    return { base, offset: checked16(offset, lineNo) };
  }

  function parseInstruction(item, labels) {
    const { line, displayLine, lineNo, pc } = item;
    const [mn, ...tail] = line.split(/\s+/), originalOp = mn.toLowerCase();
    let op = originalOp, args = splitArgs(tail.join(' '));
    const ins = { op, args, line: displayLine, lineNo, pc, modifier: !!item.modifier };
    if (!args.length && op !== 'rts' && op !== 'rti') fail(`Line ${lineNo}: missing operands`);

    if (op === 'rts' || (op === 'ba' && args[0]?.toLowerCase() === '(sp)+' && args.length === 1)) {
      if (op === 'rts' && args.length) fail(`Line ${lineNo}: RTS takes no operands`);
      ins.kind = 'rts'; return ins;
    }
    if (op === 'rti') {
      if (args.length) fail(`Line ${lineNo}: RTI takes no operands`);
      ins.kind = 'rti'; return ins;
    }
    if (op === 'swi') {
      if (args.length !== 1) fail(`Line ${lineNo}: SWI takes one immediate`);
      ins.value = resolveImmediate(args[0], labels, pc, lineNo, false);
      checked16(ins.value, lineNo, 'signed'); ins.kind = 'swi'; return ins;
    }
    if (op === 'bpr') {
      if (args.length !== 2) fail(`Line ${lineNo}: BPR needs two operands`);
      ins.rd = register(args[0]); if (ins.rd === null || ins.rd > 12) fail(`Line ${lineNo}: BPR requires R0–R12`);
      const rhs = register(args[1]);
      if (rhs !== null) { ins.rs = rhs; ins.kind = 'bpr-reg'; }
      else { ins.imm = checked16(resolveImmediate(args[1], labels, pc, lineNo, false), lineNo); ins.kind = 'bpr-imm'; }
      return ins;
    }
    if (op === 'fbpr') {
      if (args.length !== 2) fail(`Line ${lineNo}: FBPR is register-only`);
      ins.rd = requireFloatReg(args[0], lineNo); ins.rs = ins.rd; ins.rt = requireFloatReg(args[1], lineNo); ins.kind = 'fbpr'; return ins;
    }

    if (op === 'jsr') { op = 'ba.l'; args = [args[0]]; }
    if (op.endsWith('.l') && conds[op.slice(0, -2)] !== undefined) {
      ins.op = op.slice(0, -2); ins.cond = conds[ins.op]; ins.modifier = true;
      if (args.length !== 1) fail(`Line ${lineNo}: ${mn} takes one target`);
      return parseBranchTarget(ins, args[0], labels);
    }
    if (conds[op] !== undefined) {
      ins.cond = conds[op];
      if (args.length !== 1) fail(`Line ${lineNo}: ${mn} takes one target`);
      if (ins.cond === 14) fail(`Line ${lineNo}: condition 1110 is RTI, not a branch`);
      return parseBranchTarget(ins, args[0], labels);
    }
    if (op === 'ba.l') { ins.op = 'ba'; ins.cond = 15; ins.modifier = true; return parseBranchTarget(ins, args[0], labels); }

    if (op === 'ld.l') {
      if (args.length !== 2) fail(`Line ${lineNo}: LD.L syntax is LD.L Rd, imm16`);
      ins.op = 'ld'; ins.kind = 'ld-long'; ins.rd = requireDest(args[0], lineNo);
      ins.imm = checked16(resolveImmediate(args[1], labels, pc, lineNo, false), lineNo, 'unsigned');
      ins.modifier = true; return ins;
    }
    const aliases = { mulhu: 'mulh', divu: 'div', divqu: 'divq' };
    op = aliases[op] || op; ins.op = op;
    if (originalOp === 'mulhu') ins.modifier = true;
    if (originalOp === 'divu' || originalOp === 'divqu') ins.modifier = true;

    if (op === 'ld') return parseLoad(ins, args, labels);
    if (op === 'st') return parseStore(ins, args, labels);
    if (op === 'add' || op === 'sub' || op === 'adc' || op === 'sbc' || op === 'mul' || op === 'mulh' || op === 'div' || op === 'divq' || op === 'and' || op === 'or' || op === 'xor' || op === 'rol' || op === 'ror' || op === 'shl' || op === 'shr' || op === 'asr')
      return parseInteger(ins, args, labels);
    if (['fabs','fadd','fsub','fmul','fdiv','ftoi','itof'].includes(op)) return parseFloatInstruction(ins, args);
    if (op === 'b' || op === 'ba') { ins.cond = 15; if (args.length !== 1) fail(`Line ${lineNo}: ${mn} takes one target`); return parseBranchTarget(ins, args[0], labels); }
    fail(`Line ${lineNo}: unsupported instruction “${mn}”`);
  }

  function requireDest(text, lineNo) {
    const r = register(text);
    if (r === null || r > 13) fail(`Line ${lineNo}: destination must be R0–R13 (SP/PC are not general destinations)`);
    return r;
  }
  function requireFloatReg(text, lineNo) {
    const r = register(text);
    if (r === null || r < 9 || r > 12) fail(`Line ${lineNo}: floating-point operand must be F9–F12`);
    return r;
  }
  function parseBranchTarget(ins, target, labels) {
    const r = register(target);
    if (r !== null) { ins.kind = ins.cond === 14 ? 'rti' : 'branch-reg'; ins.rs = r; return ins; }
    const n = parseNum(target);
    if (n !== null) { ins.wordOffset = checked16(n, ins.lineNo); ins.kind = 'branch-imm'; return ins; }
    const key = pcLabel(target);
    if (!labels.has(key)) fail(`Line ${ins.lineNo}: unknown branch label “${target}”`);
    const delta = labels.get(key) - ins.pc;
    if (delta & 3) fail(`Line ${ins.lineNo}: branch target is not word-aligned`);
    ins.wordOffset = checked16(delta / 4, ins.lineNo); ins.targetPc = labels.get(key); ins.kind = 'branch-imm'; return ins;
  }
  function parseLoad(ins, args, labels) {
    if (args.length !== 2) fail(`Line ${ins.lineNo}: LD syntax is LD Rd, operand`);
    if (args[0].toLowerCase() === 'sp') {
      const rs = register(args[1]);
      if (rs === null) fail(`Line ${ins.lineNo}: LD SP, Rs requires a register`);
      ins.rd = 14; ins.kind = 'set-sp'; ins.rs = rs; return ins;
    }
    ins.rd = requireDest(args[0], ins.lineNo);
    if (args[1].toLowerCase() === '(sp)+' ) {
      ins.kind = 'pop'; ins.modifier = true; return ins;
    }
    const mem = parseMemory(args[1], labels, ins.pc, ins.lineNo);
    if (mem) { ins.kind = 'load'; ins.base = mem.base; ins.offset = mem.offset; return ins; }
    const r = register(args[1]);
    if (r !== null) { ins.kind = 'move'; ins.rs = r; return ins; }
    const n = parseNum(args[1]);
    if (n !== null) { ins.kind = 'ldi'; ins.imm = checked16(n, ins.lineNo, 'unsigned'); return ins; }
    const key = pcLabel(args[1]);
    if (labels.has(key)) { ins.kind = 'load'; ins.base = 15; ins.offset = checked16(labels.get(key) - ins.pc, ins.lineNo); return ins; }
    fail(`Line ${ins.lineNo}: invalid LD operand “${args[1]}”`);
  }
  function parseStore(ins, args, labels) {
    if (args.length !== 2) fail(`Line ${ins.lineNo}: ST syntax is ST address, Rs`);
    ins.src = register(args[1]);
    if (ins.src === null) fail(`Line ${ins.lineNo}: ST source must be a register`);
    const push = /^-\(sp\)$/i.test(args[0]);
    if (push) { ins.kind = 'push'; ins.modifier = true; return ins; }
    const mem = parseMemory(args[0], labels, ins.pc, ins.lineNo);
    if (!mem) fail(`Line ${ins.lineNo}: ST needs (base) or offset(base); label(base) is not supported`);
    ins.kind = 'store'; ins.base = mem.base; ins.offset = mem.offset; return ins;
  }
  function parseInteger(ins, args, labels) {
    const op = ins.op;
    if (op === 'mulh' || op === 'divq') {
      if (args.length !== 3) fail(`Line ${ins.lineNo}: ${op.toUpperCase()} needs Rd, Rs, Rt`);
      ins.rd = requireDest(args[0], ins.lineNo); ins.rs = register(args[1]); ins.rt = register(args[2]);
      if (ins.rs === null || ins.rt === null) fail(`Line ${ins.lineNo}: ${op.toUpperCase()} requires register operands`);
      if (op === 'divq' && ins.rd === ins.rs) fail(`Line ${ins.lineNo}: DIVQ requires Rd != Rs`);
      ins.kind = 'alu-rrr'; return ins;
    }
    if (args.length < 2 || args.length > 3) fail(`Line ${ins.lineNo}: ${op.toUpperCase()} needs two or three operands`);
    ins.rd = requireDest(args[0], ins.lineNo);
    if (args.length === 2) {
      const r = register(args[1]);
      if (r !== null) { ins.rs = ins.rd; ins.rt = r; ins.kind = 'alu-rr'; return ins; }
      ins.rs = ins.rd; ins.imm = resolveImmediate(args[1], labels, ins.pc, ins.lineNo);
      ins.kind = 'alu-ri'; checkedAluImmediate(ins); return ins;
    }
    ins.rs = register(args[1]);
    if (ins.rs === null) fail(`Line ${ins.lineNo}: source operand must be a register`);
    const r = register(args[2]);
    if (r !== null) { ins.rt = r; ins.kind = 'alu-rrr'; return ins; }
    ins.imm = resolveImmediate(args[2], labels, ins.pc, ins.lineNo);
    ins.kind = 'alu-rimm'; checkedAluImmediate(ins); return ins;
  }
  function checkedAluImmediate(ins) {
    const zeroExtended = ['and','or','xor','rol','ror','shl','shr','asr'].includes(ins.op) || (ins.op === 'div' && ins.modifier);
    checked16(ins.imm, ins.lineNo, zeroExtended ? 'unsigned' : 'signed');
  }
  function parseFloatInstruction(ins, args) {
    const op = ins.op;
    ins.kind = 'float';
    if (op === 'ftoi' || op === 'itof' || op === 'fabs') {
      if (args.length !== 2) fail(`Line ${ins.lineNo}: ${op.toUpperCase()} takes two register operands`);
      if (op === 'ftoi') { ins.rd = requireDest(args[0], ins.lineNo); if (ins.rd > 12) fail(`Line ${ins.lineNo}: FTOI destination must be R0–R12`); ins.rs = requireFloatReg(args[1], ins.lineNo); }
      else if (op === 'itof') { ins.rd = requireFloatReg(args[0], ins.lineNo); ins.rs = register(args[1]); if (ins.rs === null || ins.rs > 12) fail(`Line ${ins.lineNo}: ITOF source must be R0–R12`); }
      else { ins.rd = requireFloatReg(args[0], ins.lineNo); ins.rs = requireFloatReg(args[1], ins.lineNo); }
      return ins;
    }
    if (['fadd','fsub','fmul','fdiv'].includes(op)) {
      if (args.length !== 2 && args.length !== 3) fail(`Line ${ins.lineNo}: ${op.toUpperCase()} needs two or three register operands`);
      ins.rd = requireFloatReg(args[0], ins.lineNo);
      if (args.length === 2) { ins.rs = ins.rd; ins.rt = requireFloatReg(args[1], ins.lineNo); }
      else { ins.rs = requireFloatReg(args[1], ins.lineNo); ins.rt = requireFloatReg(args[2], ins.lineNo); }
      return ins;
    }
    fail(`Line ${ins.lineNo}: unsupported floating-point instruction`);
  }

  function readReg(r) { return r === 15 ? state.pc >>> 0 : state.regs[r] >>> 0; }
  function writeReg(r, value) {
    value = u32(value);
    if (r === 0) return;
    if (r === 15) fail('Only B may write PC');
    if (r === 14) fail('Only register-mode LD may write SP');
    if (r === 13) {
      const old = state.regs[13];
      const high = supervisor() ? (value & 0xc000) : (old & 0xc000);
      state.regs[13] = high | (value & SR_MASK);
    } else state.regs[r] = value;
    state.changedRegs.add(r);
  }
  function updateFlags(result, carry = null, overflow = null, clearCV = false) {
    const value = u32(result);
    let sr = flags() & ~(FLAG.N | FLAG.Z);
    if (value === 0) sr |= FLAG.Z;
    if (value & 0x80000000) sr |= FLAG.N;
    if (clearCV) sr &= ~(FLAG.C | FLAG.V);
    else {
      if (carry !== null) sr = carry ? sr | FLAG.C : sr & ~FLAG.C;
      if (overflow !== null) sr = overflow ? sr | FLAG.V : sr & ~FLAG.V;
    }
    state.regs[13] = (state.regs[13] & ~0xff) | (sr & SR_MASK);
  }
  function setCompare(a, b) {
    const result = u32(a - b), overflow = (((a ^ b) & (a ^ result) & 0x80000000) !== 0);
    updateFlags(result, a >= b, overflow);
  }
  function checkAddress(address) {
    address = u32(address);
    if (address & 3) fail(`Alignment fault at ${fmt(address)}`, 6);
    const ramWord = address + 4 <= RAM_BYTES;
    const screenWord = address >= SCREEN_BASE && address + 4 <= SCREEN_BASE + SCREEN_BYTES;
    if (!ramWord && !screenWord) fail(`Illegal data memory access at ${fmt(address)}`, 5);
    return address;
  }
  function loadWord(address) {
    address = checkAddress(address);
    return address < RAM_BYTES ? state.ram.getUint32(address, false) : state.framebuffer.getUint32(address - SCREEN_BASE, false);
  }
  function storeWord(address, value) {
    address = checkAddress(address);
    if (address < RAM_BYTES) state.ram.setUint32(address, u32(value), false);
    else state.framebuffer.setUint32(address - SCREEN_BASE, u32(value), false);
    state.changedMem.add(address);
  }
  function storeData(address, value, width) {
    for (let i = 0; i < width; i++) {
      const at = address + i;
      if ((at >= 0 && at < RAM_BYTES)) state.ram.setUint8(at, (value >>> ((width - i - 1) * 8)) & 0xff);
      else if (at >= SCREEN_BASE && at < SCREEN_BASE + SCREEN_BYTES) state.framebuffer.setUint8(at - SCREEN_BASE, (value >>> ((width - i - 1) * 8)) & 0xff);
      else fail(`Illegal data initializer at ${fmt(at)}`, 5);
      state.changedMem.add(at);
    }
  }
  function peekWord(address) { return loadWord(address); }
  function checkStackPointer(value) {
    value = u32(value);
    if ((value & 3) || value > RAM_BYTES) fail(`Stack fault: invalid SP ${fmt(value)}`, 1);
    return value;
  }
  function pushWord(value) {
    const sp = checkStackPointer(state.regs[14]);
    if (sp < 4) fail('Stack fault: stack underflow', 1);
    const next = sp - 4; storeWord(next, value); state.regs[14] = next; state.changedRegs.add(14);
  }
  function popWord() {
    const sp = checkStackPointer(state.regs[14]);
    if (sp + 4 > RAM_BYTES) fail('Stack fault: stack underflow', 1);
    const value = loadWord(sp); state.regs[14] = sp + 4; state.changedRegs.add(14); return value;
  }
  function condition(c) {
    const f = flags();
    switch (c) {
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
      case 15: return true;
      default: return false;
    }
  }
  const floatView = new DataView(new ArrayBuffer(4));
  function bitsToFloat(bits) { floatView.setUint32(0, u32(bits), false); return floatView.getFloat32(0, false); }
  function floatToBits(value) { floatView.setFloat32(0, value, false); return floatView.getUint32(0, false); }
  function setFloatFlags(bits, overflow = false, writeCarry = false) {
    let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.V);
    if ((bits & 0x7fffffff) === 0) sr |= FLAG.Z;
    if (bits & 0x80000000) sr |= FLAG.N;
    if (overflow) sr |= FLAG.V;
    if (writeCarry) sr &= ~FLAG.C;
    state.regs[13] = (state.regs[13] & ~0xff) | (sr & SR_MASK);
  }

  function executeInteger(ins) {
    const lhs = readReg(ins.kind === 'alu-rr' ? ins.rd : ins.rs);
    let rhs;
    if (ins.kind === 'alu-ri' || ins.kind === 'alu-rimm') rhs = u32(ins.imm);
    else rhs = readReg(ins.kind === 'alu-rr' ? ins.rt : ins.rt);
    const op = ins.op; let result, carry = null, overflow = null;
    if (op === 'add' || op === 'adc') {
      const cin = op === 'adc' && (flags() & FLAG.C) ? 1 : 0;
      const wide = lhs + rhs + cin; result = u32(wide); carry = wide > 0xffffffff;
      const signedWide = BigInt(sx(lhs)) + BigInt(sx(rhs)) + BigInt(cin);
      overflow = signedWide > 2147483647n || signedWide < -2147483648n;
    } else if (op === 'sub' || op === 'sbc') {
      const borrow = op === 'sbc' && !(flags() & FLAG.C) ? 1 : 0;
      result = u32(lhs - rhs - borrow); carry = BigInt(lhs) >= BigInt(rhs) + BigInt(borrow);
      const signedWide = BigInt(sx(lhs)) - BigInt(sx(rhs)) - BigInt(borrow);
      overflow = signedWide > 2147483647n || signedWide < -2147483648n;
    } else if (op === 'mul') {
      const p = BigInt(sx(lhs)) * BigInt(sx(rhs)); result = Number(BigInt.asUintN(32, p));
      overflow = p > 2147483647n || p < -2147483648n;
    } else if (op === 'mulh') {
      const p = ins.modifier ? BigInt(lhs) * BigInt(rhs) : BigInt(sx(lhs)) * BigInt(sx(rhs));
      result = Number(BigInt.asUintN(64, p) >> 32n); overflow = p > 2147483647n || p < -2147483648n;
    } else if (op === 'div' || op === 'divq') {
      overflow = false;
      if (rhs === 0) fail('Division by zero', 2);
      let q, rem;
      if (ins.modifier) { q = Math.floor(lhs / rhs); rem = lhs % rhs; }
      else {
        const a = sx(lhs), b = sx(rhs);
        if (a === -2147483648 && b === -1) { q = -2147483648; rem = 0; overflow = true; }
        else { q = Math.trunc(a / b); rem = a % b; }
      }
      result = u32(q);
      if (op === 'divq') writeReg(ins.rs, rem);
    } else if (op === 'and') result = lhs & rhs;
    else if (op === 'or') result = lhs | rhs;
    else if (op === 'xor') result = lhs ^ rhs;
    else {
      const count = rhs & 31;
      carry = null; overflow = false;
      if (op === 'shl') { result = count ? u32(lhs << count) : lhs; if (count) carry = !!((lhs >>> (32 - count)) & 1); }
      else if (op === 'shr') { result = count ? lhs >>> count : lhs; if (count) carry = !!((lhs >>> (count - 1)) & 1); }
      else if (op === 'asr') { result = count ? u32(sx(lhs) >> count) : lhs; if (count) carry = !!((lhs >>> (count - 1)) & 1); }
      else if (op === 'rol') { result = count ? u32((lhs << count) | (lhs >>> (32 - count))) : lhs; if (count) carry = !!((lhs >>> (32 - count)) & 1); }
      else if (op === 'ror') { result = count ? u32((lhs >>> count) | (lhs << (32 - count))) : lhs; if (count) carry = !!((lhs >>> (count - 1)) & 1); }
    }
    if (op === 'and' || op === 'or' || op === 'xor') updateFlags(result, null, null, true);
    else updateFlags(result, carry, overflow);
    writeReg(ins.rd, result);
  }

  function executeFloat(ins) {
    const op = ins.op;
    if (op === 'itof') {
      writeReg(ins.rd, floatToBits(sx(readReg(ins.rs)))); return;
    }
    if (op === 'ftoi') {
      const f = bitsToFloat(readReg(ins.rs));
      if (!Number.isFinite(f) || f < -2147483648 || f > 2147483647) fail('FTOI invalid or out of range', 7);
      const value = Math.trunc(f), result = u32(value);
      updateFlags(result, null, false); writeReg(ins.rd, result); return;
    }
    const a = bitsToFloat(readReg(ins.rs));
    if (op === 'fabs') {
      const bits = readReg(ins.rs) & 0x7fffffff; writeReg(ins.rd, bits); updateFlags(bits, null, false); return;
    }
    const b = bitsToFloat(readReg(ins.rt));
    if (op === 'fbpr') {
      if (Number.isNaN(a) || Number.isNaN(b)) fail('FBPR invalid comparison (NaN)', 7);
      let sr = flags() & ~(FLAG.N | FLAG.Z | FLAG.C | FLAG.V);
      if (a < b) sr |= FLAG.N;
      if (a === b) sr |= FLAG.Z;
      if (a >= b) sr |= FLAG.C;
      state.regs[13] = (state.regs[13] & ~0xff) | (sr & SR_MASK); return;
    }
    let value;
    if (op === 'fadd') value = a + b;
    else if (op === 'fsub') value = a - b;
    else if (op === 'fmul') value = a * b;
    else if (op === 'fdiv') value = a / b;
    const rounded = Math.fround(value);
    if (Number.isNaN(rounded)) fail(`${op.toUpperCase()} invalid floating-point operation`, 7);
    const bits = floatToBits(rounded), overflow = Number.isFinite(a) && Number.isFinite(b) && !Number.isFinite(rounded);
    writeReg(ins.rd, bits); setFloatFlags(bits, overflow, op === 'fadd' || op === 'fsub');
  }

  function enterException(vector, message, savedPC) {
    try {
      pushWord(savedPC);
      pushWord(state.regs[13]);
      state.regs[13] = (state.regs[13] | FLAG.S) & ~FLAG.I;
      state.changedRegs.add(13);
      // This POC has no ROM image, so the architectural frame is saved but no handler can run.
      state.trap = `${message} (vector ${vector}; ROM handler unavailable in this POC)`;
      state.halted = true;
    } catch (e) {
      state.regs[13] |= FLAG.T;
      state.trap = `Exception entry failed: ${e.message}`;
      state.halted = true;
      state.changedRegs.add(13);
    }
  }
  function reset(instructions) {
    state.regs.fill(0); state.pc = instructions.startPC ?? 0; state.cycles = 0;
    state.ram = new DataView(new ArrayBuffer(RAM_BYTES));
    state.framebuffer = new DataView(new ArrayBuffer(SCREEN_BYTES));
    state.program = instructions; state.sourceMap = new Map(instructions.map(i => [i.pc, i]));
    state.dataImage = instructions.data || [];
    state.halted = false; state.trap = null; state.changedRegs.clear(); state.changedMem.clear(); state.last = null;
    state.regs[13] = FLAG.S; // POC reset shim enters user program in supervisor mode.
    state.regs[14] = RAM_BYTES; state.regs[15] = state.pc;
    state.dataImage.forEach(({ address, value, width }) => storeData(address, value, width));
    state.changedRegs.clear(); state.changedMem.clear();
  }

  function step() {
    if (state.halted) return null;
    const ins = state.sourceMap.get(state.pc);
    if (!ins) {
      if (state.pc >= 0x8000 && state.pc <= 0x80ff) {
        state.trap = `ROM vector fetch at ${fmt(state.pc)} unavailable in this POC`; state.halted = true; return null;
      }
      const vector = state.pc >= RAM_BYTES ? 5 : 3;
      enterException(vector, `No instruction at ${fmt(state.pc)}`, state.pc); return null;
    }
    state.changedRegs.clear(); state.changedMem.clear(); state.last = ins;
    const oldPC = state.pc, oldCusr = state.regs[13];
    let nextPC = u32(oldPC + 4);
    try {
      if (nextPC < oldPC) fail('Program counter overflow', 4);
      state.cycles++;
      switch (ins.kind) {
        case 'ldi': writeReg(ins.rd, ins.imm); break;
        case 'ld-long': writeReg(ins.rd, u32((readReg(ins.rd) << 16) | ins.imm)); break;
        case 'move': writeReg(ins.rd, readReg(ins.rs)); break;
        case 'set-sp': state.regs[14] = checkStackPointer(readReg(ins.rs)); state.changedRegs.add(14); break;
        case 'load': writeReg(ins.rd, loadWord(u32(readReg(ins.base) + ins.offset))); break;
        case 'store': storeWord(u32(readReg(ins.base) + ins.offset), readReg(ins.src)); break;
        case 'push': pushWord(readReg(ins.src)); break;
        case 'pop': writeReg(ins.rd, popWord()); break;
        case 'alu-ri': case 'alu-rimm': case 'alu-rr': case 'alu-rrr': executeInteger(ins); break;
        case 'bpr-imm': setCompare(readReg(ins.rd), u32(sign16(ins.imm))); break;
        case 'bpr-reg': setCompare(readReg(ins.rd), readReg(ins.rs)); break;
        case 'fbpr': executeFloat(ins); break;
        case 'float': executeFloat(ins); break;
        case 'branch-imm':
          if (condition(ins.cond)) {
            if (ins.modifier) pushWord(nextPC);
            const target = oldPC + sign16(ins.wordOffset) * 4;
            if (target < 0 || target > 0xffffffff) fail('Program counter overflow', 4);
            nextPC = u32(target);
            if (nextPC & 3) fail(`Misaligned branch target ${fmt(nextPC)}`, 6);
          }
          break;
        case 'branch-reg':
          if (condition(ins.cond)) {
            if (ins.modifier) pushWord(nextPC);
            nextPC = readReg(ins.rs);
            if (nextPC & 3) fail(`Misaligned branch target ${fmt(nextPC)}`, 6);
          }
          break;
        case 'rts':
          nextPC = popWord();
          if (nextPC & 3) fail(`Misaligned return address ${fmt(nextPC)}`, 6);
          break;
        case 'rti': {
          if (!supervisor()) fail('RTI outside supervisor mode', 3);
          const savedCusr = popWord(), savedPC = popWord();
          state.regs[13] = savedCusr & (FLAG.S | FLAG.T | SR_MASK); state.changedRegs.add(13);
          nextPC = savedPC;
          if (nextPC & 3) fail(`Misaligned RTI address ${fmt(nextPC)}`, 6);
          break;
        }
        case 'swi':
          if (ins.value === -1 || u32(ins.value) === 0xffffffff) { state.halted = true; }
          else if (ins.value === 0) {
            state.regs.fill(0); state.regs[13] = FLAG.S; state.regs[14] = RAM_BYTES; nextPC = 0;
            state.changedRegs = new Set(Array.from({ length: 16 }, (_, i) => i));
          } else {
            // SWI service entry saves the next instruction, just like architectural entry.
            enterException(ins.value, `SWI service ${ins.value} unavailable`, nextPC);
            return ins;
          }
          break;
        default: fail(`Unsupported instruction kind ${ins.kind}`, 3);
      }
      state.pc = u32(nextPC); state.regs[15] = state.pc; state.changedRegs.add(15);
      if (state.regs[13] !== oldCusr) state.changedRegs.add(13);
      return ins;
    } catch (e) {
      enterException(e.vector || 3, e.message, oldPC);
      return ins;
    }
  }

  return { state, assemble, reset, step, fmt, parseNum, peekWord, constants: { RAM_BYTES, SCREEN_BASE, SCREEN_BYTES, FLAG } };
})();

// Browser UI, intentionally separate from the CPU core above.
const $ = id => document.getElementById(id), cpu = TDC32.state;
let timer = null, bitmapRendered = false, loadedSource = null, programFilename = 'tdc32-program.asm';
function valueDisplay(value) {
  const n = Number(value) >>> 0;
  return `<span class="hover-value" tabindex="0"><span class="value-main">${TDC32.fmt(n)}</span><span class="value-pop"><b>Hex:</b> ${TDC32.fmt(n)}<br><b>Dec:</b> ${n}<br><b>Bin:</b> ${n.toString(2).padStart(32, '0')}</span></span>`;
}
function flagUI() {
  const f = cpu.regs[13] >>> 0;
  const bits = [['T',0x8000],['S',0x4000],['I',0x20],['V',8],['C',4],['N',2],['Z',1]];
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
  $('runstate').textContent = cpu.trap ? 'ROM / TRAP STOP' : cpu.halted ? 'Halted' : timer ? 'Running' : 'Ready';
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
function trace(ins) {
  const div = document.createElement('div');
  div.innerHTML = `<span class="pc">${TDC32.fmt(ins.pc)}</span> &nbsp;${ins.line}`;
  $('trace').prepend(div);
  while ($('trace').children.length > 160) $('trace').lastChild.remove();
}
function stop() { if (timer) { clearInterval(timer); timer = null; } render(); }
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
  stop(); timer = setInterval(execute, Number($('runDelay').value) || 5); render();
};
$('stop').onclick = stop;
$('memrefresh').onclick = renderMemory;
$('memaddr').addEventListener('keydown', e => { if (e.key === 'Enter') renderMemory(); });
render();
