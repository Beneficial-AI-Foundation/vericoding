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
{ let dividend_val = Str2Int(dividend@); let divisor_val = Str2Int(divisor@); let quotient_val = dividend_val / divisor_val; let remainder_val = dividend_val % divisor_val; let quotient_vec = int_to_bit_vec(quotient_val); let remainder_vec = int_to_bit_vec(remainder_val); (quotient_vec, remainder_vec) }
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{ let s1_val = Str2Int(s1@); let s2_val = Str2Int(s2@); let product_val = s1_val * s2_val; int_to_bit_vec(product_val) }
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
{ if n == 0 { if Str2Int(sy@) == 0 { int_to_bit_vec(1) } else { int_to_bit_vec(Str2Int(sx@) % Str2Int(sz@)) } } else { let half_n = n / 2; let sy_half_len = half_n as nat + 1; let sy_left = sy.subslice(0, sy_half_len as usize); let sy_right_len = n - half_n; let sy_right = sy.subslice(sy_half_len as usize, sy_half_len as usize + sy_right_len as usize); let recurse_result_left = ModExpPow2(sx, sy_left, half_n, sz); let recurse_result_right = ModExpPow2(sx, sy_right, sy_right_len, sz); let left_val = Str2Int(recurse_result_left@); let right_val = Str2Int(recurse_result_right@); let combined_val = (left_val * right_val) % Str2Int(sz@); int_to_bit_vec(combined_val) } }
// </vc-code>

fn main() {}
}
