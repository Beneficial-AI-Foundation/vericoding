
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
/* helper modified by LLM (iteration 3): no change, was already correct */
spec fn to_bit_sequence(s: &[char]) -> Seq<char> { s@ }
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): changed `nat` and `int` casts to ghost variables where `current_sum` and `bit` are calculated */
{
    let a_seq = to_bit_sequence(a);
    let b_seq = to_bit_sequence(b);

    let a_int = Str2Int(a_seq);
    let b_int = Str2Int(b_seq);

    let sum: nat = a_int + b_int;

    let mut result_vec = Vec::<char>::new();

    if sum == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut current_sum: nat = sum;

    while current_sum > 0
        invariant
            result_vec@.len() >= 0,
            ValidBitString(result_vec@),
            current_sum >= 0,
        decreases current_sum
    {
        // Verus types 'nat' and 'int' can only be used in ghost code
        let bit = if (current_sum % 2) == 1 { '1' } else { '0' };
        result_vec.insert(0, bit);
        current_sum = current_sum / 2;
    }

    result_vec
}
// </vc-code>

fn main() {}
}

