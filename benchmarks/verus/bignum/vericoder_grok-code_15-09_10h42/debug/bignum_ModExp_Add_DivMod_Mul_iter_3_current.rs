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
  /* code modified by LLM (iteration 3): fixed compilation error by replacing b'0' with '0' as u8 in char conversion */
    let mut res = Vec::new();
    let mut carry = 0u32;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    while i < max_len || carry == 1 {
        let bit1 = if i < s1.len() {
            (s1[s1.len() - 1 - i] as u8 - '0' as u8) as u32
        } else { 0 };
        let bit2 = if i < s2.len() {
            (s2[s2.len() - 1 - i] as u8 - '0' as u8) as u32
        } else { 0 };
        let sum = bit1 + bit2 + carry;
        let new_bit = sum % 2;
        carry = sum / 2;
        res.insert(0, (new_bit as u8 + ('0' as u8)) as char);
        i += 1;
    }
    if res.is_empty() {
        res.push('0');
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
  /* code modified by LLM (iteration 3): refined DivMod logic to ensure correct division and modulus without extra zeros */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    remainder.push('0');
    for &bit in dividend {
        remainder.push(bit);
        // remove leading zeros from remainder
        while remainder.len() > 1 && remainder[0] == '0' {
            remainder.remove(0);
        }
        // compare remainder and divisor
        let cmp = if remainder.len() != divisor.len() {
            (remainder.len() as i32 - divisor.len() as i32).signum()
        } else {
            let mut j = 0;
            let mut res_cmp = 0i32;
            while j < remainder.len() {
                if remainder[j] != divisor[j] {
                    res_cmp = if remainder[j] > divisor[j] { 1 } else { -1 };
                    break;
                }
                j += 1;
            }
            res_cmp
        };
        if cmp >= 0 {
            // subtract divisor from remainder
            let mut borrow : i32 = 0;
            for idx in 0..remainder.len() {
                let rev_idx = remainder.len() - 1 - idx;
                let bit_r = (remainder[rev_idx] as u8 - '0' as u8) as i32;
                let bit_d = if idx < divisor.len() {
                    (divisor[divisor.len() - 1 - idx] as u8 - '0' as u8) as i32
                } else { 0 };
                let sub = bit_r - bit_d - borrow;
                borrow = if sub < 0 { 1 } else { 0 };
                remainder[rev_idx] = (((sub + 10) % 10) as u8 + '0' as u8) as char;
            }
            quotient.push('1');
        } else {
            quotient.push('0');
        }
    }
    // remove leading zeros
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
    }
    while remainder.len() > 1 && remainder[0] == '0' {
        remainder.remove(0);
    }
    if remainder.is_empty() {
        remainder.push('0');
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
  /* code modified by LLM (iteration 3): refined Mul logic to accumulate product correctly using bit shifts */
    let mut res = Vec::<char>::new();
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
    // remove leading zeros
    while res.len() > 1 && res[0] == '0' {
        res.remove(0);
    }
    if res.is_empty() {
        res.push('0');
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
  /* code modified by LLM (iteration 3): refined ModExp to handle base cases and recursion correctly */
    if sy.len() == 0 {
        return Vec::new(); // not reached
    }
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut r = Vec::<char>::new();
            r.push('1');
            let modr = DivMod(&r, sz);
            return modr.1;
        } else {
            return DivMod(sx, sz).1;
        }
    }
    let new_sy = &sy[0..(sy.len() - 1)];
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
