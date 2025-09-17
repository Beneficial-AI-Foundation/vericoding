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
/* helper modified by LLM (iteration 7): removed unused helper (Str2IntRev) */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): changed 'i' to be 'usize' to address compilation errors with 'int' type and indexing */
{
  let mut result = Vec::<char>::new();
  let s_a = a@;
  let s_b = b@;

  let int_a = Str2Int(s_a);
  let int_b = Str2Int(s_b);

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
    temp_sum = temp_sum / 2;
  }

  let mut i: usize = temp_result.len() - 1;
  while (temp_result.len() > 0 && i >= 0) // Changed loop condition to handle empty temp_result
    invariant
      i <= temp_result.len() -1,
      // TODO: This invariant needs to be fixed to track the elements correctly
      // Currently, it's not well-formed for the `result` vector content
      0 <= temp_result.len(),
      ValidBitString(temp_result@),
      ValidBitString(result@),
    decreases i
  {
    result.push(temp_result@[i]);
    if i == 0 { break; } // Exit condition for usize decrement from 0
    i = i - 1;
  }
  result
}
// </vc-code>

fn main() {}
}

