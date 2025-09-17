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
/* helper modified by LLM (iteration 7): Implement pow2 for shifting */
spec fn pow2(n: nat) -> nat
    decreases n
{
  if n == 0 {
    1nat
  } else {
    2nat * pow2((n - 1) as nat)
  }
}

/* helper modified by LLM (iteration 7): Fix add_binary to handle MSB first vectors by reversing for addition logic */
exec fn add_binary(a: &Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
  requires
    ValidBitString(a@),
    ValidBitString(b@)
  ensures
    ValidBitString(result@),
    Str2Int(result@) == Str2Int(a@) + Str2Int(b@)
{
  let mut a_rev = a.clone();
  a_rev.reverse();
  let mut b_rev = b.clone();
  b_rev.reverse();
  let max_len = if a_rev.len() >= b_rev.len() { a_rev.len() } else { b_rev.len() };
  let mut result = Vec::<char>::new();
  let mut carry = 0;
  let mut i = 0;
  while i < max_len
    invariant true
  {
    let b1 = if i < a_rev.len() && a_rev[i] == '1' { 1 } else { 0 };
    let b2 = if i < b_rev.len() && b_rev[i] == '1' { 1 } else { 0 };
    let sum = b1 + b2 + carry;
    let bit = if sum % 2 == 1 { '1' } else { '0' };
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

/* helper modified by LLM (iteration 7): Update shift_left to fix invariants */
exec fn shift_left(s: &Vec<char>, n: usize) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) * pow2(n as nat)
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
/* code modified by LLM (iteration 8): Fix compilation error by using concrete indexing instead of ghost seq indexing */
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
