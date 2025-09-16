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
    /* code modified by LLM (iteration 2): removed reverse() calls and used manual reversal to avoid &mut receiver restriction */
    let s1_len = s1.len();
    let s2_len = s2.len();
    let mut a: u128 = 0;
    let mut b: u128 = 0;
    let mut i: usize = 0;
    while i < s1_len {
        let bit: u128 = if s1[i] == '1' { 1 } else { 0 };
        a = a.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    i = 0;
    while i < s2_len {
        let bit: u128 = if s2[i] == '1' { 1 } else { 0 };
        b = b.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let c = a.wrapping_add(b);
    let mut tmp: Vec<char> = Vec::new();
    if c == 0 {
        return tmp;
    }
    let mut v = c;
    while v > 0 {
        let bit1 = (v & 1) == 1;
        tmp.push(if bit1 { '1' } else { '0' });
        v >>= 1;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j = tmp.len();
    while j > 0 {
        j -= 1;
        let ch = tmp[j];
        res.push(ch);
    }
    res
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
    /* code modified by LLM (iteration 2): replaced reverse() with manual reversal to satisfy verus &mut restrictions */
    let n_len = dividend.len();
    let d_len = divisor.len();
    let mut n: u128 = 0;
    let mut d: u128 = 0;
    let mut i: usize = 0;
    while i < n_len {
        let bit: u128 = if dividend[i] == '1' { 1 } else { 0 };
        n = n.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    i = 0;
    while i < d_len {
        let bit: u128 = if divisor[i] == '1' { 1 } else { 0 };
        d = d.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let q: u128 = if d == 0 { 0 } else { n / d };
    let r: u128 = if d == 0 { n } else { n % d };
    let mut qv: Vec<char> = Vec::new();
    if q > 0 {
        let mut qtmp: Vec<char> = Vec::new();
        let mut t = q;
        while t > 0 {
            let bit1 = (t & 1) == 1;
            qtmp.push(if bit1 { '1' } else { '0' });
            t >>= 1;
        }
        let mut j = qtmp.len();
        while j > 0 {
            j -= 1;
            qv.push(qtmp[j]);
        }
    }
    let mut rv: Vec<char> = Vec::new();
    if r > 0 {
        let mut rtmp: Vec<char> = Vec::new();
        let mut t2 = r;
        while t2 > 0 {
            let bit1 = (t2 & 1) == 1;
            rtmp.push(if bit1 { '1' } else { '0' });
            t2 >>= 1;
        }
        let mut k = rtmp.len();
        while k > 0 {
            k -= 1;
            rv.push(rtmp[k]);
        }
    }
    (qv, rv)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoided reverse() by manual reconstruction of big-endian bit string */
    let s1_len = s1.len();
    let s2_len = s2.len();
    let mut a: u128 = 0;
    let mut b: u128 = 0;
    let mut i: usize = 0;
    while i < s1_len {
        let bit: u128 = if s1[i] == '1' { 1 } else { 0 };
        a = a.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    i = 0;
    while i < s2_len {
        let bit: u128 = if s2[i] == '1' { 1 } else { 0 };
        b = b.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let c = a.wrapping_mul(b);
    let mut tmp: Vec<char> = Vec::new();
    if c == 0 {
        return tmp;
    }
    let mut v = c;
    while v > 0 {
        let bit1 = (v & 1) == 1;
        tmp.push(if bit1 { '1' } else { '0' });
        v >>= 1;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j = tmp.len();
    while j > 0 {
        j -= 1;
        res.push(tmp[j]);
    }
    res
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
    /* code modified by LLM (iteration 2): removed reverse() and used manual reversal; modular exponent via fast exponentiation */
    let x_len = sx.len();
    let y_len = sy.len();
    let z_len = sz.len();
    let mut x: u128 = 0;
    let mut y: u128 = 0;
    let mut z: u128 = 0;
    let mut i: usize = 0;
    while i < x_len {
        let bit: u128 = if sx[i] == '1' { 1 } else { 0 };
        x = x.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    i = 0;
    while i < y_len {
        let bit: u128 = if sy[i] == '1' { 1 } else { 0 };
        y = y.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    i = 0;
    while i < z_len {
        let bit: u128 = if sz[i] == '1' { 1 } else { 0 };
        z = z.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let modulus = if z == 0 { 1 } else { z };
    let mut base = x % modulus;
    let mut exp = y;
    let mut result: u128 = 1 % modulus;
    while exp > 0 {
        if (exp & 1) == 1 {
            result = (result.wrapping_mul(base)) % modulus;
        }
        base = (base.wrapping_mul(base)) % modulus;
        exp >>= 1;
    }
    let mut tmp: Vec<char> = Vec::new();
    if result == 0 {
        return tmp;
    }
    let mut t = result;
    while t > 0 {
        let bit1 = (t & 1) == 1;
        tmp.push(if bit1 { '1' } else { '0' });
        t >>= 1;
    }
    let mut rv: Vec<char> = Vec::new();
    let mut j = tmp.len();
    while j > 0 {
        j -= 1;
        rv.push(tmp[j]);
    }
    rv
}
// </vc-code>

fn main() {}
}
