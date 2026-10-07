// TDC32.01 CPU core and minimal program parser. No UI dependencies.
'use strict';
// CPU core: UI-independent state, parser, and one-instruction execution.
const TDC32 = (() => {
  const RAM_BYTES = 65536, WORD_MASK = 0xffffffff;
  const Z=1, N=2, C=4, V=8, X=16, S=0x4000, T=0x8000;
  const conds={beq:0,bne:1,bcs:2,bhs:2,bcc:3,blo:3,bmi:4,bpl:5,bvs:6,bvc:7,bhi:8,bls:9,bge:10,blt:11,bgt:12,ble:13,ba:15,b:15};
  const state={regs:new Uint32Array(32),sr:0,pc:0,cycles:0,ram:new DataView(new ArrayBuffer(RAM_BYTES)),program:[],sourceMap:new Map(),halted:false,trap:null,changedRegs:new Set(),changedMem:new Set(),last:null};
  const u32=n=>Number(n)>>>0, sx=n=>n|0, fmt=n=>'0x'+u32(n).toString(16).toUpperCase().padStart(8,'0');
  function fail(msg){throw Error(msg)}
  function parseNum(s){s=s.replaceAll('_','');if(/^[+-]?\d+$/.test(s))return Number(s);if(/^[+-]?0x[\da-f]+$/i.test(s))return Number(s);if(/^[+-]?\$[\da-f]+$/i.test(s))return Number(s.replace('$','0x'));if(/^[+-]?0b[01]+$/i.test(s))return Number(s);if(/^[+-]?%[01]+$/.test(s))return Number(s.replace('%','0b'));return null}
  function register(s){let m=/^(r(?:[0-9]|[12][0-9]|3[01])|sr|sp|pc)$/i.exec(s.trim());if(!m)return null;let x=m[1].toLowerCase();return x==='sr'?29:x==='sp'?30:x==='pc'?31:Number(x.slice(1))}
  function parse(source){let labels=new Map(),raw=[],pc=0;for(let [lineNo,line0] of source.split(/\r?\n/).entries()){let line=line0.replace(/;.*/, '').replace(/\/\/.*/, '').trim();if(!line)continue;let lm=line.match(/^:([\w.$]+)$/);if(lm){if(labels.has(lm[1].toLowerCase()))fail(`Line ${lineNo+1}: duplicate label ${lm[1]}`);labels.set(lm[1].toLowerCase(),pc);continue}raw.push({line,lineNo:lineNo+1,pc});pc+=4}
    const resolve=(s,lineNo)=>{let n=parseNum(s.trim());if(n!==null)return n;let label=labels.get(s.trim().replace(/^:/,'').toLowerCase());if(label===undefined)fail(`Line ${lineNo}: unknown value or label “${s}”`);return label};
    return raw.map(({line,lineNo,pc})=>{let [mn,...rest]=line.split(/\s+/),op=mn.toLowerCase(),args=rest.join(' ').split(',').map(x=>x.trim()).filter(Boolean),ins={op,args,line,lineNo,pc};if(!args.length)fail(`Line ${lineNo}: missing operands`);
      if(conds[op]!==undefined){if(args.length!==1)fail(`Line ${lineNo}: ${mn} takes one target`);ins.kind='branch';ins.cond=conds[op];ins.target=args[0];ins.link=op.endsWith('.l');return ins}
      if(op.endsWith('.l')&&conds[op.slice(0,-2)]!==undefined){ins.op=op.slice(0,-2);ins.kind='branch';ins.cond=conds[ins.op];ins.target=args[0];ins.link=true;return ins}
      if(op==='bpr'){if(args.length!==2)fail(`Line ${lineNo}: BPR needs two operands`);ins.kind='bpr';ins.rd=register(args[0]);ins.rhs=args[1];if(ins.rd===null||ins.rd>28)fail(`Line ${lineNo}: BPR needs R0–R28`);return ins}
      if(op==='swi'){ins.kind='swi';ins.value=args.length===1?resolve(args[0],lineNo):fail(`Line ${lineNo}: SWI takes one value`);return ins}
      if(op==='ba'&&args.length===1&&args[0].toLowerCase()==='(sp)+'){ins.kind='rts';return ins}
      let aliases={ldr:'ld',str:'st'};op=aliases[op]||op;ins.op=op;const alu=['ld','st','add','sub','mul','div','and','or','xor','rol','ror','shl','shr'];if(!alu.includes(op))fail(`Line ${lineNo}: unsupported instruction “${mn}”`);
      if(op==='ld'&&args.length===2&&args[0].toLowerCase()==='-(sp)'){let pushReg=register(args[1]);ins.kind='push';if(pushReg!==null){ins.pushValue=pushReg}else{ins.pushImm=resolve(args[1],lineNo)}return ins}
      if(op==='ld'&&args.length===2&&args[1].toLowerCase()==='(sp)+'){ins.kind='pop';ins.rd=register(args[0]);if(ins.rd===null||ins.rd>28)fail(`Line ${lineNo}: POP destination must be R0–R28`);return ins}
      if(op==='st'){if(args.length!==2)fail(`Line ${lineNo}: ST syntax is ST address, Rs`);ins.src=register(args[1]);if(ins.src===null||ins.src===29||ins.src===31)fail(`Line ${lineNo}: invalid store source`);let sm=args[0].match(/^(.*?)\((r(?:[0-9]|[12][0-9]|3[01])|sp|pc)\)$/i);ins.kind='st';if(sm){ins.base=register(sm[2]);ins.offset=sm[1]?resolve(sm[1],lineNo):0}else ins.address=args[0];return ins}
      if(args.length<2||args.length>3)fail(`Line ${lineNo}: ${mn} needs destination and source`);ins.rd=register(args[0]);if(ins.rd===null||ins.rd===30||ins.rd===31)fail(`Line ${lineNo}: destination must be R0–R29`);
      if(args.length===3){
ins.rs=register(args[1]);ins.imm=resolve(args[2],lineNo);if(ins.rs===null||ins.rs>28)fail(`Line ${lineNo}: source register must be R0–R28`);ins.kind='alu-ri';return ins}
      let operand=args[1],mem=operand.match(/^(.*?)\((r(?:[0-9]|[12][0-9]|3[01])|sp|pc)\)$/i);
      if(mem){ins.kind=op==='ld'?'load':'st';ins.base=register(mem[2]);ins.offset=mem[1]?resolve(mem[1],lineNo):0;if(ins.base===null)fail(`Line ${lineNo}: invalid address register`);if(op==='st'){ins.src=ins.rd;ins.rd=null}return ins}
      let r=register(operand);if(op==='ld'&&r===30){ins.kind='movsp';return ins}if(r!==null&&r<=28){ins.rs=r;ins.kind='alu-reg';return ins}
      if(op==='ld'){ins.kind='ldi';ins.value=resolve(operand,lineNo);return ins}
      fail(`Line ${lineNo}: expected register or immediate operand`);
    });
  }
  function reset(instructions){state.regs.fill(0);state.sr=0;state.pc=0;state.cycles=0;state.ram=new DataView(new ArrayBuffer(RAM_BYTES));state.program=instructions;state.sourceMap=new Map(instructions.map(i=>[i.pc,i]));state.halted=false;state.trap=null;state.changedRegs.clear();state.changedMem.clear();state.last=null;state.regs[30]=RAM_BYTES-4}
  function setFlags(result,carry=null,overflow=null,clearCV=false){result=u32(result);state.sr&=~(Z|N);if(result===0)state.sr|=Z;if(result&0x80000000)state.sr|=N;if(clearCV)state.sr&=~(C|V);else{if(carry!==null){state.sr&=~C;if(carry)state.sr|=C}if(overflow!==null){state.sr&=~V;if(overflow)state.sr|=V}}}
  function readReg(r){return r===29?state.sr>>>0:state.regs[r]>>>0}
  function writeReg(r,val){val=u32(val);if(r===0)return;if(r===29){state.sr=(val&0xff)|(state.sr&(S|T));state.changedRegs.add(29);return}if(r===30||r===31)fail(`Illegal write to ${r===30?'SP':'PC'}`);state.regs[r]=val;state.changedRegs.add(r)}
  function address(addr){addr=u32(addr);if(addr&3)fail(`Alignment fault at ${fmt(addr)}`);if(addr+4>RAM_BYTES)fail(`Illegal data memory access at ${fmt(addr)} (RAM is ${RAM_BYTES} bytes)`);return addr}
  function loadWord(addr){return state.ram.getUint32(address(addr),false)}function storeWord(addr,val){addr=address(addr);state.ram.setUint32(addr,u32(val),false);state.changedMem.add(addr)}
  function subtract(a,b){let result=u32(a-b),ov=(((a^b)&(a^result)&0x80000000)!==0);setFlags(result,a>=b,ov);return result}
  function condition(c){let f=state.sr;switch(c){case 0:return !!(f&Z);case 1:return !(f&Z);case 2:return !!(f&C);case 3:return !(f&C);case 4:return !!(f&N);case 5:return !(f&N);case 6:return !!(f&V);case 7:return !(f&V);case 8:return !!(f&C)&&!(f&Z);case 9:return !(f&C)||!!(f&Z);case 10:return !!(!!(f&N)===!!(f&V));case 11:return !!(!!(f&N)!==!!(f&V));case 12:return !(f&Z)&&!!(!!(f&N)===!!(f&V));case 13:return !!(f&Z)||!!(!!(f&N)!==!!(f&V));default:return true}}
  function operand(ins){return ins.kind==='alu-ri'?ins.imm:readReg(ins.rs)}
  function step(){if(state.halted)return null;let ins=state.sourceMap.get(state.pc);if(!ins){state.trap=`Instruction fetch outside program at ${fmt(state.pc)}`;state.halted=true;state.sr|=T;return null}state.changedRegs.clear();state.changedMem.clear();let oldpc=state.pc,oldSR=state.sr,next=u32(oldpc+4),a,b,result,addr;try{
      if(next<oldpc)fail('Program counter overflow');
      switch(ins.kind){case'ldi':writeReg(ins.rd,ins.value);break;case'movsp':writeReg(ins.rd,state.regs[30]);break;
      case'alu-reg':case'alu-ri':a=readReg(ins.rd);b=operand(ins);switch(ins.op){case'add':{let wide=a+b;result=u32(wide);setFlags(result,wide>0xffffffff,((~(a^b)&(a^result)&0x80000000)!==0));break}case'sub':result=subtract(a,b);break;case'mul':{let product=BigInt(a)*BigInt(b),signed=BigInt(sx(a))*BigInt(sx(b));result=Number(product&0xffffffffn);setFlags(result,null,signed>2147483647n||signed< -2147483648n);if((state.sr&X)&&ins.kind==='alu-reg'){writeReg(ins.rs,Number(product&0xffffffffn));result=Number((product>>32n)&0xffffffffn)}break}case'div':if(b===0)fail('Division by zero');{let q=Math.trunc(sx(a)/sx(b)),r=sx(a)%sx(b);result=u32(q);setFlags(result,null,q>2147483647||q< -2147483648);if((state.sr&X)&&ins.kind==='alu-reg')writeReg(ins.rs,r)}break;case'and':result=a&b;setFlags(result,null,null,true);break;case'or':result=a|b;setFlags(result,null,null,true);break;case'xor':result=a^b;setFlags(result,null,null,true);break;case'shl':case'shr':case'rol':case'ror':{let count=b&31,carry=false;if(count){if(ins.op==='shl'){carry=!!((a>>>(32-count))&1);result=u32(a<<count)}else if(ins.op==='shr'){carry=!!((a>>>(count-1))&1);result=a>>>count}else if(ins.op==='rol'){carry=!!((a>>>(32-count))&1);result=u32((a<<count)|(a>>>(32-count)))}else{carry=!!((a>>>(count-1))&1);result=u32((a>>>count)|(a<<(32-count)))}}else result=a;setFlags(result,carry,false);break}}writeReg(ins.rd,result);break;
      case'bpr':a=readReg(ins.rd);b=parseNum(ins.rhs);if(b===null){let target=ins.rhs.replace(/^:/,'').toLowerCase();let at=state.program.find(i=>i.label===target);b=at?at.pc:0}subtract(a,u32(b));break;
      case'branch':{let targetValue=parseNum(ins.target);let target;if(targetValue!==null)target=u32(oldpc+targetValue);else{let label=ins.target.replace(/^:/,'').toLowerCase();target=state.program.labels?.get(label)}if(target===undefined){ // labels are attached at assembly time below
          target=ins.targetPc;if(target===undefined)fail(`Unknown branch target ${ins.target}`)}
        if(condition(ins.cond)){if(ins.link){state.regs[30]=u32(state.regs[30]-4);storeWord(state.regs[30],next);state.changedRegs.add(30)}next=u32(target)}break}
      case'load':addr=u32(readReg(ins.base)+ins.offset);writeReg(ins.rd,loadWord(addr));break;
      case'st':if(ins.base!==undefined){addr=u32(readReg(ins.base)+ins.offset);storeWord(addr,readReg(ins.src))}else{addr=ins.resolvedAddress;storeWord(addr,readReg(ins.src))}break;
      case'push':state.regs[30]=u32(state.regs[30]-4);state.changedRegs.add(30);storeWord(state.regs[30],ins.pushImm===undefined?readReg(ins.pushValue):ins.pushImm);break;
      case'pop':writeReg(ins.rd,loadWord(state.regs[30]));state.regs[30]=u32(state.regs[30]+4);state.changedRegs.add(30);break;
      case'rts':next=loadWord(state.regs[30]);state.regs[30]=u32(state.regs[30]+4);state.changedRegs.add(30);break;
      case'swi':if(ins.value===-1||u32(ins.value)===0xffffffff){state.halted=true}else if(ins.value===0){state.regs.fill(0);state.sr=0;state.regs[30]=RAM_BYTES-4;state.changedRegs=new Set(Array.from({length:32},(_,i)=>i));next=0}else fail(`Unsupported SWI ${ins.value}`);break;
      default:fail(`Illegal instruction ${ins.op}`)}
      state.pc=next;state.regs[31]=next;state.changedRegs.add(31);if(state.sr!==oldSR)state.changedRegs.add(29);state.cycles++;state.last=ins;return ins;
    }catch(e){state.trap=e.message;state.halted=true;state.sr|=T;state.last=ins;return ins}}
  return {state,parse,reset,step,fmt,parseNum,constants:{RAM_BYTES,Z,N,C,V,X,S,T}};
})();
// Minimal two-pass label resolution, kept outside the execution core.
function assemble(source){let labels=new Map(),pc=0;for(let line0 of source.split(/\r?\n/)){let line=line0.replace(/;.*/, '').replace(/\/\/.*/, '').trim(),m=line.match(/^:([\w.$]+)$/);if(m)labels.set(m[1].toLowerCase(),pc);else if(line)pc+=4}let code=TDC32.parse(source);code.labels=labels;for(const ins of code){if(ins.kind==='branch'){let n=TDC32.parseNum(ins.target);if(n===null){let name=ins.target.replace(/^:/,'').toLowerCase();if(!labels.has(name))throw Error(`Line ${ins.lineNo}: unknown label “${ins.target}”`);ins.targetPc=labels.get(name)}}if(ins.kind==='bpr'){let n=TDC32.parseNum(ins.rhs);if(n===null){let name=ins.rhs.replace(/^:/,'').toLowerCase();if(!labels.has(name))throw Error(`Line ${ins.lineNo}: unknown value “${ins.rhs}”`);ins.rhs=labels.get(name)}}if(ins.kind==='st'&&ins.base===undefined){let n=TDC32.parseNum(ins.address);if(n===null){let name=ins.address.replace(/^:/,'').toLowerCase();if(!labels.has(name))throw Error(`Line ${ins.lineNo}: unknown address “${ins.address}”`);n=labels.get(name)}ins.resolvedAddress=n}}return code}


// Browser UI: kept separate from the CPU core above; no external dependencies.
'use strict';
const $=id=>document.getElementById(id), cpu=TDC32.state;let timer=null;
function flagUI(){const f=cpu.sr, flags=[['T',0x8000],['S',0x4000],['I',0x20],['X',0x10],['V',8],['C',4],['N',2],['Z',1]];$('flags').innerHTML=flags.map(([n,b])=>`<span class="flag ${f&b?'on':''}">${n}</span>`).join('')}
function render(){ $('cycles').textContent=cpu.cycles;$('pc').textContent=TDC32.fmt(cpu.pc);$('sp').textContent=TDC32.fmt(cpu.regs[30]);$('sr').textContent=TDC32.fmt(cpu.sr);$('pc').className=cpu.changedRegs.has(31)?'changed':'';$('sp').className=cpu.changedRegs.has(30)?'changed':'';$('sr').className=cpu.changedRegs.has(29)?'changed':'';$('runstate').textContent=cpu.trap?'TRAP':cpu.halted?'Halted':timer?'Running':'Ready';flagUI();$('registers').innerHTML=Array.from({length:29},(_,i)=>`<div class="reg ${cpu.changedRegs.has(i)?'changed':''}"><span>R${i}</span><b>${TDC32.fmt(cpu.regs[i])}</b></div>`).join('');let ins=cpu.sourceMap.get(cpu.pc);$('current').textContent=cpu.trap?`TRAP: ${cpu.trap}`:ins?`${TDC32.fmt(ins.pc)}  ${ins.line}`:cpu.halted?'CPU halted':'No instruction at PC';renderMemory()}
function renderMemory(){let base=TDC32.parseNum($('memaddr').value.trim());if(base===null)base=0;base=(base>>>0)&~3;if(base>=TDC32.constants.RAM_BYTES)base=0;$('memaddr').value='0x'+base.toString(16).toUpperCase();let html='<div class="memrow head"><span>Address</span><span>+0</span><span>+4</span><span>+8</span><span>+C</span></div>';for(let row=0;row<4;row++){let at=base+row*16;html+=`<div class="memrow"><span>${TDC32.fmt(at)}</span>`;for(let col=0;col<4;col++){let addr=at+col*4,val=cpu.ram.getUint32(addr,false);html+=`<span class="${cpu.changedMem.has(addr)?'changed':''}">${TDC32.fmt(val)}</span>`}html+='</div>'}$('memory').innerHTML=html}
function trace(ins){let div=document.createElement('div');div.innerHTML=`<span class="pc">${TDC32.fmt(ins.pc)}</span> &nbsp;${ins.line}`;$('trace').prepend(div);while($('trace').children.length>160)$('trace').lastChild.remove()}
function stop(){if(timer){clearInterval(timer);timer=null}render()}
function execute(){let ins=TDC32.step();if(ins)trace(ins);render();if(cpu.halted||cpu.trap)stop()}
$('reset').onclick=()=>{stop();try{let code=assemble($('source').value);TDC32.reset(code);$('trace').innerHTML='';$('message').className='message';$('message').textContent=`Loaded ${code.length} instruction${code.length===1?'':'s'}.`;render()}catch(e){$('message').className='message error';$('message').textContent=e.message}};
$('step').onclick=()=>{if(!cpu.program.length)$('reset').click();if(!cpu.halted)execute()};$('run').onclick=()=>{if(!cpu.program.length)$('reset').click();if(cpu.halted)return;stop();timer=setInterval(execute,150);render()};$('stop').onclick=stop;$('memrefresh').onclick=renderMemory;$('memaddr').addEventListener('keydown',e=>{if(e.key==='Enter')renderMemory()});render();
