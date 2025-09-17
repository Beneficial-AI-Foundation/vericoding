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

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed type mismatches by ensuring all numerical operations are performed on `nat` types, especially for `temp_sum` and its related calculations. Also, corrected the indexing of `temp_result` when pushing to `result` by converting it to a `Seq<char>` before indexing. */
{
  let mut result = Vec::<char>::new();
  let s_a = a@;
  let s_b = b@;

  let int_a = Str2Int(s_a);
  let int_b = Str2Int(s_b);

  let sum_val: nat = int_a + int_b;

  if sum_val == (0 as nat) {
    result.push('0');
    return result;
  }

  let mut temp_sum: nat = sum_val;
  let mut temp_result_vec: Vec<char> = Vec::<char>::new();

  while temp_sum > (0 as nat)
    invariant
      temp_sum >= (0 as nat),
      ValidBitString(temp_result_vec@),
    decreases temp_sum
  {
    if temp_sum % (2 as nat) == (1 as nat) {
      temp_result_vec.push('1');
    } else {
      temp_result_vec.push('0');
    }
    temp_sum = temp_sum / (2 as nat);
  }

  let temp_result_seq = temp_result_vec@;
  let mut i: int = temp_result_seq.len() as int - 1;
  while i >= 0
    invariant
      0 <= i + 1 <= temp_result_seq.len(),
      ValidBitString(temp_result_seq),
      ValidBitString(result@),
    decreases i
  {
    result.push(temp_result_seq.index(i));
    i = i - 1;
  }
  result
}
// </vc-code>

fn main() {}
}

