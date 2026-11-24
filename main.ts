// An exact implementation of make.fun's tiny stack ISA (v1) for the
// tiny-stack-vm bounty: wrapping 32-bit arithmetic and every trap code.
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Runs one program to its end and returns [output bytes, exit code].
function run(P: Buffer, inp: Buffer): [Uint8Array, number] {
  const n = P.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let pc = 0;
  let steps = 0;
  let ip = 0;
  const end = (code: number): [Uint8Array, number] => [out.subarray(0, olen), code];
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = P[pc];
    const ok =
      op <= 7 || (op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22) ||
      (op >= 0x30 && op <= 0x34) || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
    if (!ok) return end(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= n) return end(9);
    steps++;
    const next = pc + 1 + imm;
    pc = next;
    switch (op) {
      case 0x00: // HALT
        return end(0);
      case 0x01: // PUSH8, sign-extended
        if (sp === 256) return end(3);
        D[sp++] = (P[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        if (sp === 256) return end(3);
        D[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24);
        break;
      case 0x03: // POP
        if (sp < 1) return end(2);
        sp--;
        break;
      case 0x04: // DUP
        if (sp < 1) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        if (sp < 2) return end(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        if (sp < 2) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT
        if (sp < 3) return end(2);
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG
        if (sp < 1) return end(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30: // JMP
        pc = next + (((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16);
        break;
      case 0x31: // JZ
      case 0x32: { // JNZ
        if (sp < 1) return end(2);
        const v = D[--sp];
        if ((op === 0x31) === (v === 0)) pc = next + (((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16);
        break;
      }
      case 0x33: // CALL, unsigned absolute target
        if (csp === 64) return end(7);
        C[csp++] = next;
        pc = P[next - 2] | (P[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        if (sp < 1) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE
        if (sp < 2) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII
        if (sp < 1) return end(2);
        const s = '' + D[sp - 1];
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let k = 0; k < s.length; k++) out[olen++] = s.charCodeAt(k);
        break;
      }
      case 0x51: // PUTC
        if (sp < 1) return end(2);
        if (olen === 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN
        if (sp === 256) return end(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT
        if (sp < 1) return end(2);
        return end(D[--sp] & 255);
      default: { // the binary operators, 0x10-0x1e and 0x20-0x22
        if (sp < 2) return end(2);
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return end(4);
            r = b === -1 ? 0 : a % b | 0;
            break;
          case 0x15:
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return end(4);
            r = (a >>> 0) % (b >>> 0) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // 0x22 LTU
        }
        sp -= 2;
        D[sp++] = r;
      }
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const program = readFileSync(join(dir, 'program.bin'));
  const inPath = join(dir, 'input.bin');
  const input = existsSync(inPath) ? readFileSync(inPath) : Buffer.alloc(0);
  const [stdout, code] = run(program, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
