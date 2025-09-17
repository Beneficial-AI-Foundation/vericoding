
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
/* helper modified by LLM (iteration 5): no change, already correct */
spec fn to_bit_sequence(s: &[char]) -> Seq<char> { s@ }
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed ghost `nat` types to concrete `u128` types and added explicit constants */
{
    let a_seq = to_bit_sequence(a);
    let b_seq = to_bit_sequence(b);

    let a_int = Str2Int(a_seq);
    let b_int = Str2Int(b_seq);

    let sum_nat: nat = a_int + b_int;
    let mut result_vec = Vec::<char>::new();

    // Handle the case where the sum is 0
    if sum_nat == 0 {
        result_vec.push('0');
        return result_vec;
    }

    // Use a ghost variable for iteration, as `nat` cannot be directly used in `exec` code.
    // We rely on the ghost variable for termination and correctness, and perform calculations with `u128`.
    let mut ghost_current_sum = sum_nat;
    let mut current_sum_u128: u128;

    proof {
        current_sum_u128 = sum_nat as u128;
    }

    while ghost_current_sum > 0
        invariant
            result_vec@.len() as int >= 0,
            ValidBitString(result_vec@),
            ghost_current_sum >= 0,
            // Relates the ghost current_sum to the concrete u128 variable
            current_sum_u128 == ghost_current_sum as u128,
        decreases ghost_current_sum
    {
        let bit = if (current_sum_u128 % 2) == 1 { '1' } else { '0' };
        result_vec.insert(0, bit);

        ghost_current_sum = ghost_current_sum / 2;
        proof {
            current_sum_u128 = current_sum_u128 / 2;
        }
    }

    result_vec
}
// </vc-code>

fn main() {}
}

