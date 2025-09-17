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
spec fn is_power_of_two(n: nat) -> bool { exists |k: nat| n == (1 nat) << k }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let len_a = a.len();
    let len_b = b.len();

    let val_a = Str2Int(a@);
    let val_b = Str2Int(b@);

    let sum = val_a + val_b;

    let mut result_vec: Vec<char> = Vec::new();
    if sum == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut temp_sum = sum;
    while temp_sum > 0
        invariant
            temp_sum >= 0,
            ValidBitString(result_vec@ + Seq::from_fn(result_vec.len(), |j| '0')),
        decreases temp_sum
    {
        if temp_sum % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        temp_sum = temp_sum / 2;
    }

    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

