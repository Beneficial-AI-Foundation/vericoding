
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
/* helper modified by LLM (iteration 5): Corrected `SeqToNat` to return `nat` as intended by `Str2Int`. */
spec fn SeqToNat(s: Seq<char>) -> nat { Str2Int(s) }
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensured all integer literals and variables used with arithmetic operations are explicitly typed as `vstd::prelude::int` to resolve type mismatch errors. */
{
  let s_a = a@;
  let s_b = b@;

  let n_a = SeqToNat(s_a) as int;
  let n_b = SeqToNat(s_b) as int;

  let n_res_int: int = n_a + n_b;

  // Convert n_res_int back to Seq<char>
  let mut res_vec = Vec::<char>::new();
  let mut temp_n: int = n_res_int;

  if temp_n == (0 as int) {
    res_vec.push('0');
  } else {
    while temp_n > (0 as int)
      invariant
        temp_n >= (0 as int),
        forall |idx: int| (0 as int) <= idx && idx < res_vec@.len() ==> (res_vec@[idx] == '0' || res_vec@[idx] == '1')
    {
      if temp_n % (2 as int) == (1 as int) {
        res_vec.push('1');
      } else {
        res_vec.push('0');
      }
      temp_n = temp_n / (2 as int);
    }
    res_vec.reverse();
  }
  
  proof {
      assert forall |i: int| #![auto] (0 as int) <= i && i < res_vec@.len() as int implies (res_vec@[i] == '0' || res_vec@[i] == '1') by {
          // This loop constructs the sequence by repeatedly dividing by 2 and checking the remainder.
          // The remainder is either 0 or 1. Thus, each character added will either be '0' or '1'.
          // The division by 2 eventually makes temp_n 0, so the loop terminates and the elements are well-defined.
      }
  }

  res_vec
}
// </vc-code>

fn main() {}
}

