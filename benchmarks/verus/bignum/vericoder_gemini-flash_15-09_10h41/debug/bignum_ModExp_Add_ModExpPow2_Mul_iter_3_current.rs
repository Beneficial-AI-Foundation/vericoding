use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unused decreases clause, added `len_hint` to `Int2Str` helper. */
spec fn Int2Str(n: nat, len_hint: nat) -> Seq<char>
  ensures 
    ValidBitString(result),
    Str2Int(result) == n
{
  if n == 0 {
    if len_hint == 0 { seq![] } else { seq!['0'] }
  } else {
    let current_bit = if n % 2 == 1 { '1' } else { '0' };
    let remainder_seq = Int2Str(n / 2, len_hint);
    remainder_seq.add(current_bit)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Corrected `modulus_exp` by using `s_b.len()` if `s_b` is not empty, otherwise default to 1 to avoid zero exponent. Added assertion for `modulus_exp > 0`. */
{
  let s_a = a@;
  let s_b = b@;

  let val_a = Str2Int(s_a);
  let val_b = Str2Int(s_b);

  let modulus_exp = if s_b.len() == 0 { 1nat } else { s_b.len() as nat };
  assert(modulus_exp > 0);

  let mod_exp_result = ModExp(s_a, s_b, modulus_exp);
  
  let final_result = Vec::from_seq(mod_exp_result);
  final_result
}
// </vc-code>

fn main() {}
}

