// A tiny stack VM for make.fun's stack ISA (kit: generator/subject/ISA.md).
// For every /input/<id> it runs program.bin on input.bin and writes the
// program's exact output bytes and exit code to /output/<id>. Semantics are
// the ISA's own: wrapping 32-bit arithmetic, a 256-value stack, 64 return
// addresses, 256 words of memory, ten traps with their own exit codes, and
// the 1,000,000-step and 65,536-byte output limits.

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode immediate length, pops and pushes; an immediate of -1 marks a
// byte no opcode names (trap 5).
const IM = new Int8Array(256).fill(-1);
const PP = new Int8Array(256);
const PS = new Int8Array(256);
const T = (op: number, im: number, pops: number, pushes: number): void => {
  IM[op] = im;
  PP[op] = pops;
  PS[op] = pushes;
};
T(0x00, 0, 0, 0); // HALT
T(0x01, 1, 0, 1); // PUSH8
T(0x02, 4, 0, 1); // PUSH32
T(0x03, 0, 1, 0); // POP
T(0x04, 0, 1, 2); // DUP
T(0x05, 0, 2, 2); // SWAP
T(0x06, 0, 2, 3); // OVER
T(0x07, 0, 3, 3); // ROT
T(0x10, 0, 2, 1); // ADD
T(0x11, 0, 2, 1); // SUB
T(0x12, 0, 2, 1); // MUL
T(0x13, 0, 2, 1); // DIV
T(0x14, 0, 2, 1); // MOD
T(0x15, 0, 2, 1); // DIVU
T(0x16, 0, 2, 1); // MODU
T(0x17, 0, 1, 1); // NEG
T(0x18, 0, 2, 1); // AND
T(0x19, 0, 2, 1); // OR
T(0x1a, 0, 2, 1); // XOR
T(0x1b, 0, 1, 1); // NOT
T(0x1c, 0, 2, 1); // SHL
T(0x1d, 0, 2, 1); // SHR
T(0x1e, 0, 2, 1); // SHRU
T(0x20, 0, 2, 1); // EQ
T(0x21, 0, 2, 1); // LT
T(0x22, 0, 2, 1); // LTU
T(0x30, 2, 0, 0); // JMP
T(0x31, 2, 1, 0); // JZ
T(0x32, 2, 1, 0); // JNZ
T(0x33, 2, 0, 0); // CALL
T(0x34, 0, 0, 0); // RET
T(0x40, 0, 1, 1); // LOAD
T(0x41, 0, 2, 0); // STORE
T(0x50, 0, 1, 0); // PRINT
T(0x51, 0, 1, 0); // PUTC
T(0x52, 0, 0, 1); // IN
T(0x53, 0, 1, 0); // EXIT

function run(P: Buffer, inp: Buffer): { out: Buffer; exit: number } {
  const n = P.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let sp = 0;
  let csp = 0;
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const end = (exit: number): { out: Buffer; exit: number } => ({ out: Buffer.from(buf.subarray(0, olen)), exit });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = P[pc]!;
    const im = IM[op]!;
    if (im < 0) return end(5);
    if (pc + im >= n) return end(9);
    steps++;
    const nx = pc + 1 + im;
    if (sp < PP[op]!) return end(2);
    if (sp - PP[op]! + PS[op]! > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        D[sp++] = (P[nx - 1]! << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = P[nx - 4]! | (P[nx - 3]! << 8) | (P[nx - 2]! << 16) | (P[nx - 1]! << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1]!;
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1]!;
        D[sp - 1] = D[sp - 2]!;
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2]!;
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3]!;
        D[sp - 3] = D[sp - 2]!;
        D[sp - 2] = D[sp - 1]!;
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = -D[sp - 1]! | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1]!;
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = D[sp - 1]!;
        const a = D[sp - 2]!;
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : a % b | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = (a >>> 0) % (b >>> 0) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        D[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((P[nx - 2]! | (P[nx - 1]! << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp]!;
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = P[nx - 2]! | (P[nx - 1]! << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp]!;
        break;
      case 0x40: {
        const a = D[sp - 1]!;
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a]!;
        break;
      }
      case 0x41: {
        const a = D[sp - 1]!;
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2]!;
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]!);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) buf[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return end(11);
        buf[olen++] = D[--sp]! & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++]! : -1;
        break;
      case 0x53:
        return end(D[--sp]! & 255);
      default:
        return end(5);
    }
  }
}

// The driver: every instance in the input directory, answered in name order,
// each in its own output directory, whatever its program does.
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp: Buffer;
  try {
    inp = readFileSync(join(I, id, 'input.bin'));
  } catch {
    inp = Buffer.alloc(0);
  }
  const r = run(readFileSync(join(I, id, 'program.bin')), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.exit}\n`);
}
