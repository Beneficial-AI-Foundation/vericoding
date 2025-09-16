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
/* helper modified by LLM (iteration 10): Fixed compilation error by using i32 instead of int for loop index in add_binary */
spec fn pow2(n: nat) -> nat
    decreases n
{
  if n == 0 {
    1nat
  } else {
    2nat * pow2((n - 1) as nat)
  }
}

exec fn add_binary(a: &Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
  requires
    ValidBitString(a@),
    ValidBitString(b@)
  ensures
    ValidBitString(result@),
    Str2Int(result@) == Str2Int(a@) + Str2Int(b@)
{
  let a_len = a.len();
  let b_len = b.len();
  let max_len = if a_len < b_len { b_len } else { a_len };
  let mut i = 0;
  let mut carry = 0;
  let mut temp = Vec::<char>::new();
  while i < max_len
    invariant true
  {
    let a_bit = if i < a_len && a[a_len - 1 - i] == '1' { 1 } else { 0 };
    let b_bit = if i < b_len && b[b_len - 1 - i] == '1' { 1 } else { 0 };
    let sum = a_bit + b_bit + carry;
    let bit = if sum % 2 == 1 { '1' } else { '0' };
    temp.push(bit);
    carry = sum / 2;
    i += 1;
  }
  if carry == 1 {
    temp.push('1');
  }
  let mut result_vec = Vec::<char>::new();
  let temp_len = temp.len();
  let mut j: i32 = (temp_len as i32) - 1;
  while j >= 0
    invariant true
  {
    result_vec.push(temp[j as usize]);
    j -= 1;
  }
  while result_vec.len() > 1 && result_vec[0] == '0' {
    result_vec.remove(0);
  }
  if result_vec.is_empty() {
    result_vec.push('0');
  }
  result_vec
}

exec fn shift_left(s: &Vec<char>, n: usize) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures
    ValidBitString(res@),
    Str2Int(res@) == Str2Int(s@) * pow2(n as nat)
{
  let mut shifted = s.clone();
  let mut count = 0;
  while count < n
    invariant
      count <= n,
      ValidBitString(shifted@)
  {
    shifted.push('0');
    count += 1;
  }
  shifted
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 10): No changes, relying on fixed helpers */
  let mut res: Vec<char> = Vec::new();
  let len = s2.len();
  let mut pos: usize = 0;
  while pos < len
    invariant true
  {
    let bit_index = len - 1 - pos;
    if s2[bit_index] == '1' {
      let s1_vec = s1.to_vec();
      let shifted_s1 = shift_left(&s1_vec, pos);
      res = add_binary(&res, &shifted_s1);
    }
    pos += 1;
  }
  while res.len() > 1 && res[0] == '0' {
    res.remove(0);
  }
  if res.len() == 0 {
    res.push('0');
  }
  res
}
// </vc-code>

fn main() {}
}
