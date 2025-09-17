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
/* helper modified by LLM (iteration 2): Changed return type of Str2IntRev to nat. */
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
/* code modified by LLM (iteration 2): Cast temp_sum to nat and ensured type consistency. reversed pushed element to fix order. */
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

  let mut temp_sum: nat = sum_val;
  let mut temp_result = Vec::<char>::new();

  while temp_sum > 0
    invariant
      temp_sum >= 0,
      ValidBitString(temp_result@),
    decreases temp_sum
  {
    if temp_sum % 2 == 1 {
      temp_result.push('1');
    } else {
      temp_result.push('0');
    }
    temp_sum = (temp_sum / 2) as nat;
  }

  let mut i = temp_result.len() as int - 1;
  while i >= 0
    invariant
      i >= -1,
      i < temp_result.len() as int,
      result.len() + i + 1 == temp_result.len() as int,
      forall |j: int| 0 <= j && j < result.len() ==> result@[j] == temp_result@[temp_result.len() as int - 1 - j],
    decreases i
  {
    result.push(temp_result@[i]);
    i = i - 1;
  }
  result
}
// </vc-code>

fn main() {}
}

