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
/* helper modified by LLM (iteration 9): Fixed `Seq::<char>::new()` to pass `0` for length argument; fixed `spec_shl` by replacing with `pow2` from `vstd`. */
spec fn multiply_bit_strings_spec(s1: Seq<char>, s2: Seq<char>) -> (result: Seq<char>)
  requires ValidBitString(s1),
           ValidBitString(s2)
  ensures ValidBitString(result),
          Str2Int(result) == Str2Int(s1) * Str2Int(s2)
{
  let num1 = Str2Int(s1);
  let num2 = Str2Int(s2);
  let product = num1 * num2;

  if product == 0 {
    seq!['0']
  } else {
    let mut result_seq = Seq::<char>::new(0, |i| ' ' /* dummy char */);
    let mut temp_product = product;
    while temp_product > 0
      invariant
        temp_product >= 0,
        ValidBitString(result_seq),
        product == Str2Int(result_seq) + temp_product * (vstd::multiset::pow2(result_seq.len() as nat)),
    {
      if temp_product % 2 == 1 {
        result_seq = seq!['1'] + result_seq;
      } else {
        result_seq = seq!['0'] + result_seq;
      }
      temp_product = temp_product / 2;
    }
    // reverse the string to get the correct order (LSB to MSB)
    let mut final_result_seq = Seq::<char>::new(0, |i| ' ' /* dummy char */);
    let mut j: int = result_seq.len() as int - 1;
    while j >= 0
      invariant
        j >= -1,
        j < result_seq.len() as int,
        final_result_seq.len() == (result_seq.len() as int - 1 - j) as nat,
        forall |k: int| 0 <= k && k < final_result_seq.len() as int ==> final_result_seq.index(k) == result_seq.index(result_seq.len() as int - 1 - k),
        ValidBitString(final_result_seq)
    {
      final_result_seq = final_result_seq.push(result_seq.index(j as nat));
      j = j -1;
    }
    final_result_seq
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed type mismatch in while condition (usize vs nat) and added `use std::ops::Index;` */
{
  use std::ops::Index;
  let res_seq = multiply_bit_strings_spec(s1@, s2@);
  let mut res_vec = Vec::<char>::new();
  let mut i: usize = 0;
  while (i as nat) < res_seq.len()
    invariant
      0 <= i,
      (i as nat) <= res_seq.len(),
      (res_vec.len() as nat) == (i as nat),
      forall |j: int| 0 <= j && j < i as int ==> #[trigger] res_vec.index(j as usize) == res_seq.index(j as nat),
      ValidBitString(res_vec@)
  {
    // The index(i) extracts the character as a ghost value implicitly convertible to a concrete char.
    res_vec.push(res_seq.index(i as nat));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}


