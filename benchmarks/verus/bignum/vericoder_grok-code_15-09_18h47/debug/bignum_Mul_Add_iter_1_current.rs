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
spec fn pow2(n: nat) -> nat
decreases n
{
  if n == 0 {
    1
  } else {
    2nat * pow2(n - 1)
  }
}

exec fn add_binary(a: &Vec<char>, b: &Vec<char>) -> Vec<char>
  requires
    ValidBitString(a@),
    ValidBitString(b@)
  ensures
    ValidBitString(result@),
    Str2Int(result@) == Str2Int(a@) + Str2Int(b@)
{
  let max_len = if a.len() >= b.len() { a.len() } else { b.len() };
  let mut result = Vec::new();
  let mut carry = 0;
  let mut i = 0;
  while i < max_len
    invariant
      result.len() == i
  {
    let b1 = if i < a.len() {
      if a@[a.len() - 1 - i] == '1' {
        1
      } else {
        0
      }
    } else {
      0
    };
    let b2 = if i < b.len() {
      if b@[b.len() - 1 - i] == '1' {
        1
      } else {
        0
      }
    } else {
      0
    };
    let sum = b1 + b2 + carry;
    let bit = if sum % 2 == 1 {
      '1'
    } else {
      '0'
    };
    result.push(bit);
    carry = sum / 2;
    i += 1;
  }
  if carry > 0 {
    result.push('1');
  }
  result.reverse();
  result
}

exec fn shift_left(s: &Vec<char>, n: usize) -> Vec<char>
  requires ValidBitString(s@)
  ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s@) * pow2(n as nat)
{
  let mut res = s.clone();
  let mut count = 0;
  while count < n
    invariant count <= n, res.len() == s@.len() + count
  {
    res.push('0');
    count +=1;
  }
  res
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  if s1.len() == 0 {
    return Vec::new();
  }
  if s2.len() == 0 {
    return Vec::new();
  }
  let mut res = Vec::new();
  let len2 = s2.len();
  let mut pos = 0;
  while pos < len2 {
    let bit_index = len2 - 1 - pos;
    if s2[bit_index] == '1' {
      let shifted_s1 = shift_left(s1, pos);
      res = add_binary(&res, &shifted_s1);
    }
    pos += 1;
  }
  while res.len() > 1 && res@[0] == '0' {
    res.erase(0);
  }
  res
}
// </vc-code>

fn main() {}
}
