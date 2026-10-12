const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');

const source = fs.readFileSync('tdc32-core.js', 'utf8');
const marker = '// Browser UI, intentionally separate from the CPU core above.';
const context = {};
vm.runInNewContext(source.slice(0, source.indexOf(marker)) + '\nglobalThis.cpu = TDC32;', context);
const cpu = context.cpu;

function loadProgram(assembly) {
  const program = cpu.assemble(assembly);
  cpu.reset(program);
  assert.equal(cpu.state.pc, cpu.constants.ROM_BASE, 'reset starts at the ROM boot vector');
  assert.equal(cpu.peekWord(0), cpu.constants.ROM_BASE, 'reset vector points to boot ROM');
  assert.notEqual(cpu.peekWord(cpu.constants.ROM_BASE), 0, 'boot ROM is present and inspectable');
  cpu.step();
  cpu.step();
  assert.equal(cpu.state.pc, program.startPC, 'boot ROM launches the assembled program');
  return program;
}

// Low system page is reserved; ordinary assembly starts at $0400.
const basic = cpu.assemble('SWI 63');
assert.equal(basic.startPC, cpu.constants.RAM_START);
assert.throws(() => cpu.assemble('.adr $0200\n.u32 1'), /not mapped RAM or video memory/);
cpu.reset(basic);
assert.equal(cpu.peekWord(cpu.constants.SYS.SSP), 0x4000);
assert.equal(cpu.peekWord(cpu.constants.SYS.USP), cpu.constants.RAM_BYTES);
assert.equal(cpu.peekWord(cpu.constants.IO.BOARD_ID), 0x54444332);
const html = fs.readFileSync('index.html', 'utf8');
const defaultSource = html.match(/<textarea id="source"[^>]*>([\s\S]*?)<\/textarea>/)[1];
const defaultProgram = cpu.assemble(defaultSource);
cpu.reset(defaultProgram);
for (let i = 0; i < 32 && !cpu.state.halted; i++) cpu.step();
assert.equal(cpu.state.halted, true, 'default UI program boots and halts normally');
assert.equal(cpu.state.regs[1], 0xffffffff);

loadProgram('SWI 63');
assert.throws(() => cpu.peekWord(cpu.constants.SYS.SSP), /supervisor-only/);

loadProgram('LD R1, $0200(R0)\nSWI 63');
cpu.setKey(cpu.constants.KEY.LEFT, true);
cpu.step();
assert.equal(cpu.state.regs[1], cpu.constants.KEY.LEFT, 'keyboard state is readable by user code');
cpu.setKey(cpu.constants.KEY.LEFT, false);
assert.equal(cpu.peekWord(cpu.constants.IO.KEY_STATE), 0, 'key-up clears the held-key bit');
assert.throws(() => cpu.peekWord(0x0300), /Unassigned system-page address/);

loadProgram('LD R1, $8000\nLD R1, (R1)');
cpu.step(); cpu.step();
assert.match(cpu.state.lastException, /vector 5/, 'ROM cannot be read as ordinary data');

loadProgram('LD R1, 123\n:loop\nBA loop');
for (let i = 0; i < cpu.constants.CYCLES_PER_FRAME + 32 && !cpu.state.halted; i++) cpu.step();
assert.equal(cpu.state.frameCount, 1, 'virtual video clock advances at the defined instruction cadence');
assert.equal(cpu.state.irqPending, 0, 'default ROM IRQ handler acknowledges VBL');
assert.equal(cpu.state.regs[1], 123, 'IRQ handler preserves the interrupted general register');
assert.equal(cpu.state.regs[14], cpu.constants.RAM_BYTES, 'RTI restores the user stack bank');
assert.equal(cpu.state.supervisorSP, 0x4000, 'IRQ frame is removed from the supervisor stack');
assert.equal(cpu.state.regs[13] & cpu.constants.FLAG.S, 0, 'RTI returns to user mode');
assert.equal(cpu.state.trap, null);

loadProgram('SWI 3');
cpu.step();
assert.equal(cpu.state.pc, cpu.constants.ROM_BASE + 0x100, 'software interrupt dispatches through the vector table');
cpu.step();
assert.equal(cpu.state.halted, true, 'minimal fatal ROM handler stops on an unhandled exception');
assert.match(cpu.state.lastException, /vector 3/);
assert.equal(cpu.state.ram.getUint32(0x3ff8, false), cpu.constants.FLAG.I, 'exception frame stores CUSR at the supervisor stack top');
assert.equal(cpu.state.ram.getUint32(0x3ffc, false), 0x404, 'SWI frame stores the next PC below CUSR');

const ioProgram = cpu.assemble(fs.readFileSync('examples/io-board-test.asm', 'utf8'));
cpu.reset(ioProgram); cpu.step(); cpu.step();
cpu.setKey(cpu.constants.KEY.FIRE, true);
for (let i = 0; i < 8; i++) cpu.step();
assert.equal(cpu.peekWord(0x4000), cpu.constants.KEY.FIRE, 'I/O test program records held-key state in RAM');

const cube = cpu.assemble(fs.readFileSync('examples/rotating-cube.asm', 'utf8'));
cpu.reset(cube);
cpu.setKey(cpu.constants.KEY.LEFT, true);
let framebufferWrites = 0;
for (let i = 0; i < cpu.constants.CYCLES_PER_FRAME + 512 && !cpu.state.halted && !cpu.state.trap; i++) {
  cpu.step();
  if ([...cpu.state.changedMem].some(address => address >= cpu.constants.SCREEN_BASE)) framebufferWrites++;
}
assert.equal(cpu.state.trap, null);
assert.ok(framebufferWrites > 0, 'cube demo writes to the framebuffer after VBL');
assert.equal(cpu.peekWord(0x146c4), 0x000001f9, 'Left input selects the previous pre-rendered angle');

cpu.reset(cube);
cpu.setKey(cpu.constants.KEY.FIRE, true);
for (let i = 0; i < cpu.constants.CYCLES_PER_FRAME + 512 && !cpu.state.halted && !cpu.state.trap; i++) cpu.step();
assert.equal(cpu.peekWord(0x146c4), 0x000000ff, 'Space disables auto-rotation and holds the current angle');

const ball = cpu.assemble(fs.readFileSync('examples/bouncing-ball.asm', 'utf8'));
cpu.reset(ball);
let steps = 0;
while (cpu.state.frameCount < 40 && steps < 1200000 && !cpu.state.halted && !cpu.state.trap) { cpu.step(); steps++; }
for (let i = 0; i < 512 && !cpu.state.halted && !cpu.state.trap; i++) cpu.step();
assert.equal(cpu.state.frameCount, 40);
assert.equal(cpu.state.trap, null);
const pixelByte = (xCell, yCell, scanline = 0) => cpu.state.framebuffer.getUint8((yCell * 8 + scanline) * 80 + xCell);
assert.equal(pixelByte(78, 48), 0x18, 'round ball has bounced and is visible after 40 VBLs');
assert.equal(pixelByte(78, 48, 2), 0x7e, 'ball sprite has a rounded middle row');
assert.equal(pixelByte(79, 49), 0, 'previous ball position was erased');

console.log('Virtual computer tests passed.');
