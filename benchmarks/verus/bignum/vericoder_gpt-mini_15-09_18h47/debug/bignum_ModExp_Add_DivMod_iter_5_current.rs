use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): binary addition implemented with carry, trimming leading zeros */
    // perform binary addition from least significant bit to most
    let mut i1: usize = s1.len();
    let mut i2: usize = s2.len();
    let mut res_rev: Vec<char> = Vec::new();
    let mut carry: u8 = 0;
    while i1 > 0 || i2 > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
        decreases (i1 + i2)
    {
        let b1: u8 = if i1 > 0 && s1[i1 - 1] == '1' { 1 } else { 0 };
        let b2: u8 = if i2 > 0 && s2[i2 - 1] == '1' { 1 } else { 0 };
        let sum: u8 = b1 + b2 + carry;
        let bit: char = if sum % 2 == 1 { '1' } else { '0' };
        res_rev.push(bit);
        carry = if sum >= 2 { 1 } else { 0 };
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }
    if carry == 1 {
        res_rev.push('1');
    }

    // reverse to MSB-first
    let mut res: Vec<char> = Vec::new();
    let mut idx: usize = res_rev.len();
    while idx > 0
        invariant
            idx <= res_rev.len(),
        decreases idx
    {
        res.push(res_rev[idx - 1]);
        idx -= 1;
    }

    // trim leading zeros
    let mut first_one: usize = 0;
    while first_one < res.len() && res[first_one] == '0'
        invariant
            first_one <= res.len(),
        decreases (res.len() - first_one)
    {
        first_one += 1;
    }

    if first_one == res.len() {
        Vec::<char>::new()
    } else if first_one == 0 {
        res
    } else {
        let mut out: Vec<char> = Vec::new();
        let mut k: usize = first_one;
        while k < res.len()
            invariant
                k <= res.len(),
            decreases (res.len() - k)
        {
            out.push(res[k]);
            k += 1;
        }
        out
    }
}

// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): long division on bit-vectors using compare/subtract helpers */
    // helper: trim leading zeros
    fn trim(mut v: Vec<char>) -> Vec<char> {
        let mut i: usize = 0;
        while i < v.len() && v[i] == '0' {
            i += 1;
        }
        if i == 0 { v } else {
            let mut out: Vec<char> = Vec::new();
            let mut k: usize = i;
            while k < v.len() {
                out.push(v[k]);
                k += 1;
            }
            out
        }
    }

    // helper: compare two MSB-first bit vectors (after trimming)
    fn cmp(a: &Vec<char>, b: &Vec<char>) -> i8 {
        let mut i1: usize = 0;
        while i1 < a.len() && a[i1] == '0' { i1 += 1; }
        let mut j1: usize = 0;
        while j1 < b.len() && b[j1] == '0' { j1 += 1; }
        let la = a.len() - i1;
        let lb = b.len() - j1;
        if la > lb { return 1; }
        if la < lb { return -1; }
        let mut k: usize = 0;
        while k < la {
            let ca = a[i1 + k];
            let cb = b[j1 + k];
            if ca == '1' && cb == '0' { return 1; }
            if ca == '0' && cb == '1' { return -1; }
            k += 1;
        }
        0
    }

    // helper: subtract b from a (a >= b), both MSB-first, returns trimmed result
    fn sub(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
        // reverse to LSB-first for easy subtraction
        let mut ra: Vec<char> = Vec::new();
        let mut i: usize = 0;
        while i < a.len() { ra.push(a[a.len() - 1 - i]); i += 1; }
        let mut rb: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < b.len() { rb.push(b[b.len() - 1 - j]); j += 1; }
        let mut out_rev: Vec<char> = Vec::new();
        let mut borrow: u8 = 0;
        let mut k: usize = 0;
        while k < ra.len() {
            let ba: u8 = if ra[k] == '1' { 1 } else { 0 };
            let bb: u8 = if k < rb.len() && rb[k] == '1' { 1 } else { 0 };
            let mut v: i8 = (ba as i8) - (bb as i8) - (borrow as i8);
            if v < 0 { v += 2; borrow = 1; } else { borrow = 0; }
            out_rev.push(if v == 1 { '1' } else { '0' });
            k += 1;
        }
        // reverse back and trim
        let mut out: Vec<char> = Vec::new();
        let mut t: usize = out_rev.len();
        while t > 0 { out.push(out_rev[t - 1]); t -= 1; }
        // trim
        let mut p: usize = 0;
        while p < out.len() && out[p] == '0' { p += 1; }
        if p == out.len() { Vec::<char>::new() } else {
            let mut res: Vec<char> = Vec::new();
            let mut q: usize = p;
            while q < out.len() { res.push(out[q]); q += 1; }
            res
        }
    }

    // copy inputs to Vec<char>
    let mut dividend_v: Vec<char> = Vec::new();
    let mut ii: usize = 0;
    while ii < dividend.len() { dividend_v.push(dividend[ii]); ii += 1; }
    let mut divisor_v: Vec<char> = Vec::new();
    let mut jj: usize = 0;
    while jj < divisor.len() { divisor_v.push(divisor[jj]); jj += 1; }

    // long division
    let mut quotient: Vec<char> = Vec::new();
    let mut rem: Vec<char> = Vec::new();

    let mut idxd: usize = 0;
    while idxd < dividend_v.len()
        invariant
            idxd <= dividend_v.len(),
        decreases (dividend_v.len() - idxd)
    {
        // append next bit
        if rem.len() == 0 && dividend_v[idxd] == '0' {
            // keep rem empty
        } else {
            rem.push(dividend_v[idxd]);
        }
        // compare rem and divisor
        if rem.len() == 0 {
            quotient.push('0');
        } else {
            let c = cmp(&rem, &divisor_v);
            if c >= 0 {
                quotient.push('1');
                rem = sub(&rem, &divisor_v);
            } else {
                quotient.push('0');
            }
        }
        idxd += 1;
    }

    // trim quotient and remainder
    let q_trim = trim(quotient);
    let r_trim = trim(rem);
    (q_trim, r_trim)
}

// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): modular exponentiation using repeated squaring with vector multiply and modulo by DivMod */
    // helpers: trim leading zeros
    fn trim(mut v: Vec<char>) -> Vec<char> {
        let mut i: usize = 0;
        while i < v.len() && v[i] == '0' { i += 1; }
        if i == 0 { v } else if i == v.len() { Vec::<char>::new() } else {
            let mut out: Vec<char> = Vec::new();
            let mut k: usize = i;
            while k < v.len() { out.push(v[k]); k += 1; }
            out
        }
    }

    // multiply two bit-vectors (MSB-first) using Add
    fn mul(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
        let mut result: Vec<char> = Vec::new(); // zero
        let mut i: usize = 0;
        while i < b.len()
            invariant
                i <= b.len(),
            decreases (b.len() - i)
        {
            // process from LSB (end)
            let idx = b.len() - 1 - i;
            if b[idx] == '1' {
                // shifted a by i (append i zeros at end)
                let mut shifted: Vec<char> = Vec::new();
                let mut k: usize = 0;
                while k < a.len() { shifted.push(a[k]); k += 1; }
                let mut z: usize = 0;
                while z < i { shifted.push('0'); z += 1; }
                result = Add(result.as_slice(), shifted.as_slice());
            }
            i += 1;
        }
        trim(result)
    }

    // convert inputs to Vec<char>
    let mut base: Vec<char> = Vec::new();
    let mut xi: usize = 0;
    while xi < sx.len() { base.push(sx[xi]); xi += 1; }
    let mut exp: Vec<char> = Vec::new();
    let mut yi: usize = 0;
    while yi < sy.len() { exp.push(sy[yi]); yi += 1; }
    let mut modu: Vec<char> = Vec::new();
    let mut zi: usize = 0;
    while zi < sz.len() { modu.push(sz[zi]); zi += 1; }

    // initialize result = 1 mod m
    let mut result: Vec<char> = Vec::new();
    // represent 1 as single '1'
    result.push('1');
    result = DivMod(result.as_slice(), modu.as_slice()).1;

    // exponentiation by squaring: process bits from LSB to MSB
    let mut k: usize = 0;
    while k < exp.len()
        invariant
            k <= exp.len(),
        decreases (exp.len() - k)
    {
        let bit = exp[exp.len() - 1 - k];
        if bit == '1' {
            // result = (result * base) % modu
            let prod = mul(&result, &base);
            let r = DivMod(prod.as_slice(), modu.as_slice()).1;
            result = r;
        }
        // base = (base * base) % modu
        let b2 = mul(&base, &base);
        base = DivMod(b2.as_slice(), modu.as_slice()).1;
        k += 1;
    }

    trim(result)
}

// </vc-code>

fn main() {}
}


