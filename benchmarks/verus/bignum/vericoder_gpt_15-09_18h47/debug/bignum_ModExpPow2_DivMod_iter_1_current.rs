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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut a: u128 = 0;
    let mut i: usize = 0;
    while i < dividend.len() {
        a = a * 2 + if dividend[i] == '1' { 1 } else { 0 };
        i += 1;
    }
    let mut b: u128 = 0;
    let mut j: usize = 0;
    while j < divisor.len() {
        b = b * 2 + if divisor[j] == '1' { 1 } else { 0 };
        j += 1;
    }
    let q = a / b;
    let r = a % b;
    let mut qv: Vec<char> = Vec::new();
    if q == 0 {
        qv.push('0');
    } else {
        let mut tmp = q;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0 {
            let bit = (tmp & 1) as u8;
            bits.push(if bit == 1 { '1' } else { '0' });
            tmp >>= 1;
        }
        let mut k: isize = bits.len() as isize - 1;
        while k >= 0 {
            qv.push(bits[k as usize]);
            k -= 1;
        }
    }
    let mut rv: Vec<char> = Vec::new();
    if r == 0 {
        rv.push('0');
    } else {
        let mut tmp = r;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0 {
            let bit = (tmp & 1) as u8;
            bits.push(if bit == 1 { '1' } else { '0' });
            tmp >>= 1;
        }
        let mut k: isize = bits.len() as isize - 1;
        while k >= 0 {
            rv.push(bits[k as usize]);
            k -= 1;
        }
    }
    (qv, rv)
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    let mut x: u128 = 0;
    let mut i: usize = 0;
    while i < sx.len() {
        x = x * 2 + if sx[i] == '1' { 1 } else { 0 };
        i += 1;
    }
    let mut y: u128 = 0;
    let mut j: usize = 0;
    while j < sy.len() {
        y = y * 2 + if sy[j] == '1' { 1 } else { 0 };
        j += 1;
    }
    let mut z: u128 = 0;
    let mut k: usize = 0;
    while k < sz.len() {
        z = z * 2 + if sz[k] == '1' { 1 } else { 0 };
        k += 1;
    }
    let mut res_val: u128 = 1 % z;
    if y == 0 {
        res_val = 1 % z;
    } else {
        let mut base = x % z;
        let mut exp = y;
        let mut acc: u128 = 1 % z;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = (acc * base) % z;
            }
            base = (base * base) % z;
            exp >>= 1;
        }
        res_val = acc;
    }
    let mut res_vec: Vec<char> = Vec::new();
    if res_val == 0 {
        res_vec.push('0');
    } else {
        let mut tmp = res_val;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0 {
            let bit = (tmp & 1) as u8;
            bits.push(if bit == 1 { '1' } else { '0' });
            tmp >>= 1;
        }
        let mut t: isize = bits.len() as isize - 1;
        while t >= 0 {
            res_vec.push(bits[t as usize]);
            t -= 1;
        }
    }
    res_vec
}
// </vc-code>

fn main() {}
}


