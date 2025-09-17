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
/* helper modified by LLM (iteration 4): Removed Seq::singleton from helper as it is not needed */
spec fn Int2Str(n: nat)
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    let digit = if n % 2 == 0 { '0' } else { '1' };
    Int2Str(n / 2).push(digit)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Changed `to_vec()` to `into_vec()` to resolve a compilation error */
{
  let a_nat = Str2Int(a@);
  let b_nat = Str2Int(b@);

  let result_nat = a_nat + b_nat;

  let result_seq = Int2Str(result_nat);
  result_seq.into_vec()
}
// </vc-code>

fn main() {}
}

