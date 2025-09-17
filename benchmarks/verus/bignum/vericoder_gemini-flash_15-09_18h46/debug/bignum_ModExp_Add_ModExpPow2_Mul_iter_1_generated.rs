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
spec fn Str2IntRev(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    let first_char_val = if s.index(0) == '1' { 1nat } else { 0nat };
    first_char_val + 2 * Str2IntRev(s.subrange(1, s.len() as int))
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let mut result = Vec::<char>::new();
  let s_a = a@;
  let s_b = b@;

  let int_a = Str2IntRev(s_a);
  let int_b = Str2IntRev(s_b);

  let sum_val = int_a + int_b;

  if sum_val == 0 {
    result.push('0');
    return result;
  }

  let mut temp_sum = sum_val;

  while temp_sum > 0
    invariant
      temp_sum >= 0,
    decreases temp_sum
  {
    if temp_sum % 2 == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    temp_sum = temp_sum / 2;
  }

  result.reverse();
  result
}
// </vc-code>

fn main() {}
}

