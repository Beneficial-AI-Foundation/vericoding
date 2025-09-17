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
/* helper modified by LLM (iteration 5): added `char_to_digit` and `digit_to_char` helpers */
spec fn char_to_digit(c: char) -> nat
  requires c == '0' || c == '1'
{
  if c == '0' { 0nat } else { 1nat }
}

spec fn digit_to_char(d: nat) -> char
  requires d == 0 || d == 1
{
  if d == 0 { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Switched from `int` to `usize` for loop indices and array access to fix compilation errors */
{
  let n = s1.len();
  let m = s2.len();
  if n == 0 || m == 0 {
    let mut res = Vec::<char>::new();
    res.push('0');
    return res;
  }

  let mut result_vec = Vec::<char>::new();
  let res_len = n + m;
  for _i in 0..res_len {
    result_vec.push('0');
  }

  let mut i: usize = m - 1;
  loop
    invariant
      0 <= i + 1 <= m,
      result_vec.len() == res_len,
      forall |k: int| 0 <= k < result_vec.len() ==> (result_vec@[k] == '0' || result_vec@[k] == '1'),
    decreases i + 1
  {
    let mut carry: u8 = 0;
    if s2[i] == '1' {
      let mut j: usize = n - 1;
      loop
        invariant
          0 <= j + 1 <= n,
          result_vec.len() == res_len,
          forall |k: int| 0 <= k < result_vec.len() ==> (result_vec@[k] == '0' || result_vec@[k] == '1'),
          0 <= carry <= 1,
        decreases j + 1
      {
        let sum = (s1[j] as u8 - b'0') as u8
                  + (result_vec[i + j + 1] as u8 - b'0') as u8
                  + carry;
        result_vec[i + j + 1] = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        if j == 0 { break; }
        j = j - 1;
      }
      result_vec[i] = ((result_vec[i] as u8 - b'0' + carry) as char);
    }
    if i == 0 { break; }
    i = i - 1;
  }

  let mut first_one = 0;
  while first_one < res_len - 1 && result_vec[first_one] == '0'
    invariant
      0 <= first_one < res_len,
      result_vec.len() == res_len,
      forall |k: int| 0 <= k < result_vec.len() ==> (result_vec@[k] == '0' || result_vec@[k] == '1'),
  {
    first_one = first_one + 1;
  }

  let mut final_res = Vec::<char>::new();
  let mut k = first_one;
  while k < res_len
    invariant
      first_one <= k <= res_len,
      final_res.len() == (k - first_one) as nat,
      result_vec.len() == res_len,
      forall |l: int| 0 <= l < final_res.len() ==> (final_res@[l] == '0' || final_res@[l] == '1'),
      forall |l: int| 0 <= l < final_res.len() ==> final_res@[l] == result_vec@[first_one + l],
  {
    final_res.push(result_vec[k]);
    k = k + 1;
  }
  final_res
}
// </vc-code>

fn main() {}
}
