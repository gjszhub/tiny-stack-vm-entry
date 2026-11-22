// Tiny stack VM for make.fun's tiny-stack-vm-01 (ISA.md in the kit).
// Runs every bytecode program in /input/<id>/ and writes its output + exit code.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [immediate bytes, pops, pushes] for each opcode; an opcode not listed is unknown.
const SPEC = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2],
  5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  16: [0, 2, 1], 17: [0, 2, 1], 18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1],
  21: [0, 2, 1], 22: [0, 2, 1], 23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1],
  26: [0, 2, 1], 27: [0, 1, 1], 28: [0, 2, 1], 29: [0, 2, 1], 30: [0, 2, 1],
  32: [0, 2, 1], 33: [0, 2, 1], 34: [0, 2, 1],
  48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0], 51: [2, 0, 0], 52: [0, 0, 0],
  64: [0, 1, 1], 65: [0, 2, 0],
  80: [0, 1, 0], 81: [0, 1, 0], 82: [0, 0, 1], 83: [0, 1, 0],
};

// Runs one bytecode program on its input bytes; returns what it wrote and its exit code.
function execute(prog, input) {
  const n = prog.length;
  const stk = new Int32Array(256);
  let sp = 0;
  const ret = new Int32Array(64);
  let rp = 0;
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let bl = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code) => ({ bytes: buf.slice(0, bl), code });
  for (;;) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const spec = SPEC[op];
    if (spec === undefined) return finish(5);
    const imm = spec[0], need = spec[1], give = spec[2];
    if (pc + imm >= n) return finish(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < need) return finish(2);
    if (sp - need + give > 256) return finish(3);
    pc = nx;
    if (op === 0) return finish(0);
    if (op === 1) { stk[sp++] = (prog[nx - 1] << 24) >> 24; continue; }
    if (op === 2) { stk[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); continue; }
    if (op === 3) { sp--; continue; }
    if (op === 4) { stk[sp] = stk[sp - 1]; sp++; continue; }
    if (op === 5) { const t = stk[sp - 1]; stk[sp - 1] = stk[sp - 2]; stk[sp - 2] = t; continue; }
    if (op === 6) { stk[sp] = stk[sp - 2]; sp++; continue; }
    if (op === 7) { const t = stk[sp - 3]; stk[sp - 3] = stk[sp - 2]; stk[sp - 2] = stk[sp - 1]; stk[sp - 1] = t; continue; }
    if (op >= 16 && op <= 34) {
      if (op === 23) { stk[sp - 1] = -stk[sp - 1] | 0; continue; }
      if (op === 27) { stk[sp - 1] = ~stk[sp - 1]; continue; }
      const b = stk[sp - 1];
      const a = stk[sp - 2];
      let r;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2;
      stk[sp++] = r;
      continue;
    }
    if (op === 48 || op === 49 || op === 50) {
      const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
      let take = op === 48;
      if (op !== 48) { const v = stk[--sp]; take = op === 49 ? v === 0 : v !== 0; }
      if (take) pc = nx + rel;
      continue;
    }
    if (op === 51) {
      if (rp === 64) return finish(7);
      ret[rp++] = nx;
      pc = prog[nx - 2] | (prog[nx - 1] << 8);
      continue;
    }
    if (op === 52) {
      if (rp === 0) return finish(8);
      pc = ret[--rp];
      continue;
    }
    if (op === 64) {
      const addr = stk[sp - 1];
      if (addr < 0 || addr >= 256) return finish(6);
      stk[sp - 1] = mem[addr];
      continue;
    }
    if (op === 65) {
      const addr = stk[sp - 1];
      const v = stk[sp - 2];
      if (addr < 0 || addr >= 256) return finish(6);
      sp -= 2;
      mem[addr] = v;
      continue;
    }
    if (op === 80) {
      const text = Buffer.from(String(stk[sp - 1]));
      if (bl + text.length > 65536) return finish(11);
      sp--;
      buf.set(text, bl);
      bl += text.length;
      continue;
    }
    if (op === 81) {
      if (bl + 1 > 65536) return finish(11);
      buf[bl++] = stk[--sp] & 255;
      continue;
    }
    if (op === 82) { stk[sp++] = ip < input.length ? input[ip++] : -1; continue; }
    if (op === 83) return finish(stk[--sp] & 255);
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inDir).sort()) {
  if (!statSync(join(inDir, id)).isDirectory()) continue;
  const prog = readFileSync(join(inDir, id, 'program.bin'));
  const input = readFileSync(join(inDir, id, 'input.bin'));
  const r = execute(prog, input);
  mkdirSync(join(outDir, id), { recursive: true });
  writeFileSync(join(outDir, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(outDir, id, 'exit.txt'), `${r.code}\n`);
}
