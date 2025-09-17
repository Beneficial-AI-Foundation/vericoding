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
/* helper modified by LLM (iteration 4): Removed helper section to focus on fixing the code which was causing compilation errors. Helper functions will be added in a later turn if needed. */
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Added decreases clause to loop where `temp_product` is reduced. This resolves the verification error regarding the missing decreases clause. Removed `assume(false)` within the proof block; it was a verification bypass. The current focus is on fixing existing verification errors and not yet on providing full functional correctness proofs. */
{
  let n_s1 = s1.len();
  let n_s2 = s2.len();

  let mut val1: u128 = 0;
  for i in 0..n_s1 {
    if s1[i] == '1' {
      val1 |= (1u128 << (n_s1 - 1 - i));
    }
  }

  let mut val2: u128 = 0;
  for i in 0..n_s2 {
    if s2[i] == '1' {
      val2 |= (1u128 << (n_s2 - 1 - i));
    }
  }

  let product = val1 * val2;

  let mut res_vec: Vec<char> = Vec::new();
  if product == 0 {
    res_vec.push('0');
  } else {
    let mut temp_product = product;
    while temp_product > 0
      decreases temp_product
    {
      if temp_product & 1 == 1 {
        res_vec.push('1');
      } else {
        res_vec.push('0');
      }
      temp_product >>= 1;
    }
    
    // Manually reverse res_vec as Vec::reverse() is not supported by Verus
    let mut reversed_res_vec: Vec<char> = Vec::new();
    let mut k = res_vec.len();
    while k > 0
      decreases k
    {
      k -= 1;
      reversed_res_vec.push(res_vec[k]);
    }
    res_vec = reversed_res_vec;
  }

  res_vec
}
// </vc-code>

fn main() {}
}
