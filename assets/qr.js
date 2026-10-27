/* QR-kode-generator (byte-tilstand, UTF-8). Bygget efter QR-standarden ISO/IEC 18004.
   QR.make(tekst, 'L'|'M'|'Q'|'H') -> {size, get(x, y) -> bool} */
(function(){
const ECC = { // kodeord pr. blok og antal blokke, version 1-40
  L: [[-1,7,10,15,20,26,18,20,24,30,18,20,24,26,30,22,24,28,30,28,28,28,28,30,30,26,28,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
      [-1,1,1,1,1,1,2,2,2,2,4,4,4,4,4,6,6,6,6,7,8,8,9,9,10,12,12,12,13,14,15,16,17,18,19,19,20,21,22,24,25]],
  M: [[-1,10,16,26,18,24,16,18,22,22,26,30,22,22,24,24,28,28,26,26,26,26,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28],
      [-1,1,1,1,2,2,4,4,4,5,5,5,8,9,9,10,10,11,13,14,16,17,17,18,20,21,23,25,26,28,29,31,33,35,37,38,40,43,45,47,49]],
  Q: [[-1,13,22,18,26,18,24,18,22,20,24,28,26,24,20,30,24,28,28,26,30,28,30,30,30,30,28,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
      [-1,1,1,2,2,4,4,6,6,8,8,8,10,12,16,12,17,16,18,21,20,23,23,25,27,29,34,34,35,38,40,43,45,48,51,53,56,59,62,65,68]],
  H: [[-1,17,28,22,16,22,28,26,26,24,28,24,28,22,24,24,30,28,28,26,28,30,24,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
      [-1,1,1,2,4,4,4,5,6,8,8,11,11,16,16,18,16,19,21,25,25,25,34,30,32,35,37,40,42,45,48,51,54,57,60,63,66,70,74,77,81]]
};
const FMT = {L: 1, M: 0, Q: 3, H: 2};
function rawModules(v){ let r = (16*v + 128)*v + 64; if (v >= 2) { const a = Math.floor(v/7) + 2; r -= (25*a - 10)*a - 55; if (v >= 7) r -= 36; } return r; }
const dataCodewords = (v, e) => Math.floor(rawModules(v)/8) - ECC[e][0][v]*ECC[e][1][v];
function gmul(x, y){ let z = 0; for (let i = 7; i >= 0; i--) { z = (z << 1) ^ ((z >>> 7) * 0x11D); z ^= ((y >>> i) & 1) * x; } return z & 255; }
function rsDivisor(deg){ const r = new Array(deg).fill(0); r[deg-1] = 1; let root = 1; for (let i = 0; i < deg; i++) { for (let j = 0; j < deg; j++) { r[j] = gmul(r[j], root); if (j + 1 < deg) r[j] ^= r[j+1]; } root = gmul(root, 2); } return r; }
function rsRemainder(data, div){ const r = div.map(() => 0); for (const b of data) { const f = b ^ r.shift(); r.push(0); div.forEach((c, i) => { r[i] ^= gmul(c, f); }); } return r; }
function alignPos(v, size){ if (v === 1) return []; const n = Math.floor(v/7) + 2, step = Math.floor((v*8 + n*3 + 5) / (n*4 - 4)) * 2, r = [6]; for (let p = size - 7; r.length < n; p -= step) r.splice(1, 0, p); return r; }

function make(text, ecl){
  ecl = ecl || 'M';
  const bytes = Array.from(new TextEncoder().encode(text));
  let v = 1;
  for (;; v++) {
    if (v > 40) throw new Error('For meget tekst til en QR-kode');
    const cc = v <= 9 ? 8 : 16;
    if (4 + cc + bytes.length*8 <= dataCodewords(v, ecl)*8) break;
  }
  const cc = v <= 9 ? 8 : 16, cap = dataCodewords(v, ecl)*8, bits = [];
  const put = (val, n) => { for (let i = n - 1; i >= 0; i--) bits.push((val >>> i) & 1); };
  put(4, 4); put(bytes.length, cc); for (const b of bytes) put(b, 8);
  put(0, Math.min(4, cap - bits.length)); put(0, (8 - bits.length % 8) % 8);
  for (let p = 0xEC; bits.length < cap; p ^= 0xEC ^ 0x11) put(p, 8);
  const data = []; for (let i = 0; i < bits.length; i += 8) { let b = 0; for (let j = 0; j < 8; j++) b = (b << 1) | bits[i+j]; data.push(b); }
  // Fejlrettelse og fletning af blokke
  const nb = ECC[ecl][1][v], ecLen = ECC[ecl][0][v], raw = Math.floor(rawModules(v)/8), nShort = nb - raw % nb, shortLen = Math.floor(raw / nb), div = rsDivisor(ecLen), blocks = [];
  for (let i = 0, k = 0; i < nb; i++) { const d = data.slice(k, k + shortLen - ecLen + (i < nShort ? 0 : 1)); k += d.length; const e = rsRemainder(d, div); if (i < nShort) d.push(0); blocks.push(d.concat(e)); }
  const all = []; for (let i = 0; i < blocks[0].length; i++) for (let j = 0; j < nb; j++) if (i !== shortLen - ecLen || j >= nShort) all.push(blocks[j][i]);
  // Tegn mønstret
  const size = v*4 + 17, M = [], F = [];
  for (let y = 0; y < size; y++) { M.push(new Array(size).fill(false)); F.push(new Array(size).fill(false)); }
  const fn = (x, y, d) => { M[y][x] = d; F[y][x] = true; };
  for (let i = 0; i < size; i++) { fn(6, i, i % 2 === 0); fn(i, 6, i % 2 === 0); }
  const finder = (x, y) => { for (let dy = -4; dy <= 4; dy++) for (let dx = -4; dx <= 4; dx++) { const d = Math.max(Math.abs(dx), Math.abs(dy)), xx = x + dx, yy = y + dy; if (xx >= 0 && yy >= 0 && xx < size && yy < size) fn(xx, yy, d !== 2 && d !== 4); } };
  finder(3, 3); finder(size - 4, 3); finder(3, size - 4);
  const ap = alignPos(v, size);
  for (let i = 0; i < ap.length; i++) for (let j = 0; j < ap.length; j++) {
    if ((i === 0 && j === 0) || (i === 0 && j === ap.length - 1) || (i === ap.length - 1 && j === 0)) continue;
    for (let dy = -2; dy <= 2; dy++) for (let dx = -2; dx <= 2; dx++) fn(ap[i] + dx, ap[j] + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
  }
  const drawFormat = mask => {
    const d = FMT[ecl] << 3 | mask; let r = d; for (let i = 0; i < 10; i++) r = (r << 1) ^ ((r >>> 9) * 0x537);
    const b = (d << 10 | r) ^ 0x5412, bit = i => ((b >>> i) & 1) === 1;
    for (let i = 0; i <= 5; i++) fn(8, i, bit(i));
    fn(8, 7, bit(6)); fn(8, 8, bit(7)); fn(7, 8, bit(8));
    for (let i = 9; i < 15; i++) fn(14 - i, 8, bit(i));
    for (let i = 0; i < 8; i++) fn(size - 1 - i, 8, bit(i));
    for (let i = 8; i < 15; i++) fn(8, size - 15 + i, bit(i));
    fn(8, size - 8, true);
  };
  drawFormat(0);
  if (v >= 7) { let r = v; for (let i = 0; i < 12; i++) r = (r << 1) ^ ((r >>> 11) * 0x1F25); const b = v << 12 | r;
    for (let i = 0; i < 18; i++) { const bt = ((b >>> i) & 1) === 1, a = size - 11 + i % 3, c = Math.floor(i / 3); fn(a, c, bt); fn(c, a, bt); } }
  let i = 0;
  for (let right = size - 1; right >= 1; right -= 2) {
    if (right === 6) right = 5;
    for (let vert = 0; vert < size; vert++) for (let j = 0; j < 2; j++) {
      const x = right - j, up = ((right + 1) & 2) === 0, y = up ? size - 1 - vert : vert;
      if (!F[y][x] && i < all.length*8) { M[y][x] = ((all[i >>> 3] >>> (7 - (i & 7))) & 1) === 1; i++; }
    }
  }
  const maskFn = [(x, y) => (x + y) % 2 === 0, (x, y) => y % 2 === 0, x => x % 3 === 0, (x, y) => (x + y) % 3 === 0,
    (x, y) => (Math.floor(x/3) + Math.floor(y/2)) % 2 === 0, (x, y) => x*y % 2 + x*y % 3 === 0,
    (x, y) => (x*y % 2 + x*y % 3) % 2 === 0, (x, y) => ((x + y) % 2 + x*y % 3) % 2 === 0];
  const applyMask = m => { for (let y = 0; y < size; y++) for (let x = 0; x < size; x++) if (!F[y][x] && maskFn[m](x, y)) M[y][x] = !M[y][x]; };
  const penalty = () => {
    let p = 0, dark = 0;
    for (let k = 0; k < 2; k++) for (let a = 0; a < size; a++) {
      let run = 1, line = [];
      for (let b = 0; b < size; b++) { const c = k ? M[b][a] : M[a][b]; line.push(c ? 1 : 0); if (b && c === (k ? M[b-1][a] : M[a][b-1])) { run++; if (run === 5) p += 3; else if (run > 5) p++; } else run = 1; }
      const s = '0000' + line.join('') + '0000'; for (const pat of ['00001011101', '10111010000']) { let q = s.indexOf(pat); while (q >= 0) { p += 40; q = s.indexOf(pat, q + 1); } }
    }
    for (let y = 0; y < size - 1; y++) for (let x = 0; x < size - 1; x++) { const c = M[y][x]; if (c === M[y][x+1] && c === M[y+1][x] && c === M[y+1][x+1]) p += 3; }
    for (const r of M) for (const c of r) if (c) dark++;
    p += Math.floor(Math.abs(dark*20 - size*size*10) / (size*size)) * 10;
    return p;
  };
  let best = 0, bp = Infinity;
  for (let m = 0; m < 8; m++) { applyMask(m); drawFormat(m); const p = penalty(); if (p < bp) { bp = p; best = m; } applyMask(m); }
  applyMask(best); drawFormat(best);
  return {size, version: v, get: (x, y) => x >= 0 && y >= 0 && x < size && y < size && M[y][x]};
}
window.QR = {make};
})();
