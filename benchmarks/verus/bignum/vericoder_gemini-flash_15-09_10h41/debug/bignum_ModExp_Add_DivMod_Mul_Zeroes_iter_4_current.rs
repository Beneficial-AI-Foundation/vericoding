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
/* helper modified by LLM (iteration 4): Removed unnecessary adds and `Seq::empty().push` patterns in favor of `Seq::singleton` */
spec fn add(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    ValidBitString(add(s1, s2)),
    Str2Int(add(s1,s2)) == Str2Int(s1) + Str2Int(s2),
  decreases s1.len() + s2.len()
{
  if s1.len() == 0 && s2.len() == 0 {
    return Seq::<char>::empty();
  } else if s1.len() == 0 {
    return s2;
  } else if s2.len() == 0 {
    return s1;
  }

  let head1 = s1.index(s1.len() as int - 1);
  let head2 = s2.index(s2.len() as int - 1);
  let rest1 = s1.subrange(0, s1.len() as int - 1);
  let rest2 = s2.subrange(0, s2.len() as int - 1);

  let (sum_bit, carry_bit) = if head1 == '1' && head2 == '1' {
    ('0', '1')
  } else if head1 == '0' && head2 == '0' {
    ('0', '0')
  } else if (head1 == '1' && head2 == '0') || (head1 == '0' && head2 == '1') {
    ('1', '0')
  } else {
    ('0', '0') // should not happen with ValidBitString
  };

  let carry_seq = if carry_bit == '1' {
    Seq::singleton('1')
  } else {
    Seq::<char>::empty()
  };

  let recur_sum = add(carry_seq, add(rest1, rest2));
  return recur_sum.push(sum_bit);
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type error with `i as int` */
{
  let s1 = a@;
  let s2 = b@;

  let result_seq = add(s1, s2);

  let mut res_vec = Vec::<char>::new();
  let mut i: int = 0;
  while i < result_seq.len()
    invariant
      result_seq.len() >= 0,
      i >= 0,
      i <= result_seq.len(),
      res_vec.len() == i,
      forall |j: int| 0 <= j && j < i ==> res_vec.index(j) == result_seq.index(j),
  {
    res_vec.push(result_seq.index(i));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}

