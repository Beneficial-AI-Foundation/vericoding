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
    let mut res = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    let mut max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    while i < max_len || carry == 1 
    {
        let bit1 = if i < s1.len() {
            (s1[s1.len() - 1 - i] as u8 - '0' as u8) as u32
        } else { 0 };
        let bit2 = if i < s2.len() {
            (s2[s2.len() - 1 - i] as u8 - '0' as u8) as u32
        } else { 0 };
        let sum = bit1 + bit2 + carry;
        let new_bit = sum % 2;
        carry = sum / 2;
        res.insert(0, (new_bit as u8 + '0' as u8) as char);
        if res.len() > max_len + 1 {
            max_len = res.len() - 1;
        }
        i += 1;
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
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    remainder.push('0');
    for &bit in s1 {
        remainder.push(bit);
        // remove leading zeros from remainder
        while remainder.len() > 1 && remainder[0] == '0' {
            remainder = (&remainder[1..]).to_vec();
        }
        // compare remainder and s2
        let cmp = {
            if remainder.len() > s2.len() {
                1 as i32
            } else if remainder.len() < s2.len() {
                -1 as i32
            } else {
                let mut j = 0;
                while j < remainder.len() {
                    if remainder[j] > s2[j] {
                        break 1 as i32
                    } else if remainder[j] < s2[j] {
                        break -1 as i32
                    }
                    j += 1;
                }
                0 as i32
            }
        };
        if cmp >= 0 {
            // sub s2 from remainder
            let mut borrow = 0;
            let mut idx = 0;
            while idx < remainder.len() {
                let bit_r = (remainder[remainder.len() - 1 - idx] as u8 - '0' as u8) as u32;
                let bit_div = if idx < s2.len() {(s2[s2.len() - 1 - idx] as u8 - '0' as u8) as u32} else { 0 };
                let sub = bit_r as i32 - bit_div as i32 - borrow;
                if sub < 0 {
                    remainder[remainder.len() - 1 - idx] = ((sub as u32 + 10) % 10 + '0' as u32) as char;
                    borrow = 1;
                } else {
                    remainder[remainder.len() - 1 - idx] = ((sub as u32 ) % 10 + '0' as u32) as char;
                    borrow = 0;
                }
                idx += 1;
            }
            quotient.push('1');
        } else {
            quotient.push('0');
        }
    }
    // remove leading zeros
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient = (&quotient[1..]).to_vec();
    }
    while remainder.len() > 1 && remainder[0] == '0' {
        remainder = (&remainder[1..]).to_vec();
    }
    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    res.push('0');
    for k in 0..s2.len() {
        if s2[s2.len() - 1 - k] == '1' {
            let mut shifted = s1.to_vec();
            for _ in 0..k {
                shifted.push('0');
            }
            res = Add(&res, &shifted);
        }
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
    if sy.len() == 0 {
        return Vec::new(); // error case, but requires >0
    }
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut r = Vec::new();
            r.push('1');
            let modr = DivMod(&r, sz).
            return modr.1;
        } else {
            return DivMod(sx, sz).1;
        }
    }
    let new_sy = &sy[..sy.len() - 1];
    let recur = ModExp(sx, new_sy, sz);
    let ex2 = Mul(sx, sx);
    let sx2mod = DivMod(&ex2, sz).1;
    if sy[sy.len() - 1] == '1' {
        let res = Mul(&recur, &sx);
        DivMod(&res, sz).1
    } else {
        recur
    }
}
// </vc-code>

fn main() {}
}
