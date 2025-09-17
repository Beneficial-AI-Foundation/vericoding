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
    let mut carry = 0u8;
    let mut result = Vec::new();
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + carry as nat * Exp_int(2, i as nat) == (Str2Int(s1@.subrange(0, i.min(s1.len()) as int)) + Str2Int(s2@.subrange(0, i.min(s2.len()) as int))),
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum & 1 == 1 { '1' } else { '0' });
        carry = sum >> 1;
        i = i + 1;
    }
    result
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
    for c in dividend.iter() {
        remainder.push(*c);
    }
    let divisor_val = Str2Int(divisor@);
    while Str2Int(remainder@) >= divisor_val
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(dividend@) == Str2Int(quotient@) * divisor_val + Str2Int(remainder@),
            Str2Int(remainder@) < divisor_val || remainder@.len() > 0,
    {
        let sub_result = Sub(&remainder, divisor);
        remainder = sub_result;
        quotient = Add(&quotient, &vec!['1']);
    }
    (quotient, remainder)
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
    if Str2Int(sy@) == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    let y_minus_pow = Sub(sy, &vec!['1']);
    let rec_result = ModExpPow2(sx, &y_minus_pow, n - 1, sz);
    let squared = Mul(&rec_result, &rec_result);
    let (_, remainder) = DivMod(&squared, sz);
    remainder
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push('0');
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int)),
    {
        result = Add(&result, &result);
        if s2[i] == '1' {
            result = Add(&result, s1);
        }
        i = i + 1;
    }
    result
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
    if sy.len() == 1 && sy[0] == '0' {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    let last_bit = sy[sy.len() - 1];
    let y_div_2 = &sy[..sy.len() - 1];
    let half_exp = ModExp(sx, y_div_2, sz);
    let squared = Mul(&half_exp, &half_exp);
    let (_, mod_squared) = DivMod(&squared, sz);
    if last_bit == '1' {
        let mul_x = Mul(&mod_squared, sx);
        let (_, final_mod) = DivMod(&mul_x, sz);
        final_mod
    } else {
        mod_squared
    }
}
// </vc-code>

fn main() {}
}
