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
/* helper modified by LLM (iteration 5): No changes to helper, it was not the source of the error */
spec fn add(a_int: nat, b_int: nat) -> nat { a_int + b_int }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch errors by ensuring all variables are explicitly `nat` where expected. This mostly involved casting return values of operations to `nat` if they were implicitly `int` previously. */
{
    let a_int = Str2Int(a@);
    let b_int = Str2Int(b@);
    let sum_nat: nat = add(a_int, b_int) as nat;

    let mut result_vec = Vec::new();
    if sum_nat == 0 {
        result_vec.push('0');
    }
    let mut temp_sum: nat = sum_nat;
    while temp_sum > 0
        invariant (temp_sum == 0 && result_vec@.len() == 0) || (temp_sum > 0 && ValidBitString(result_vec@))
        decreases temp_sum
    {
        if (temp_sum % 2) == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        temp_sum = (temp_sum / 2) as nat;
    }
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

