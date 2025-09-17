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
/* helper modified by LLM (iteration 2): Removed previous helper, as it was not necessary. */
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed compilation errors related to `nat` type in execution context by using `u8` and then converting to `char` */
{
  let n = s1.len();
  let m = s2.len();
  let mut result_vec = Vec::new();
  if n == 0 || m == 0 {
    result_vec.push('0');
    return result_vec;
  }

  let mut res_len = n + m;
  for _i in 0..res_len {
    result_vec.push('0');
  }

  for i in (0..m).rev() {
    let mut carry: u8 = 0;
    if s2[i] == '1' {
      for j in (0..n).rev() {
        let sum = (s1[j] as u8 - b'0')
                  + (result_vec[i + j + 1] as u8 - b'0')
                  + carry;
        result_vec[i + j + 1] = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
      }
      result_vec[i] = ((result_vec[i] as u8 - b'0' + carry) as char);
    }
  }

  let mut first_one = 0;
  while first_one < res_len - 1 && result_vec[first_one] == '0' {
    first_one = first_one + 1;
  }

  let mut final_res = Vec::new();
  for i in first_one..res_len {
    final_res.push(result_vec[i]);
  }
  final_res
}
// </vc-code>

fn main() {}
}
