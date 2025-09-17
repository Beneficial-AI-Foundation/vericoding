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
/* helper modified by LLM (iteration 2): Fixed types for Seq operations and removed `Seq::single` as it doesn't exist. */
spec fn helper_add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    ValidBitString(result),
{ তত্ত্ব
  let l1 = s1.len();
  let l2 = s2.len();
  let max_len = if l1 > l2 { l1 } else { l2 };

  let mut result_seq = new_str_repr_seq(max_len + 1);
  let mut carry = 0 nat;

  let mut i = 0 nat;
  while i < max_len
    invariant
      0 <= i,
      i <= max_len,
      carry == 0 || carry == 1,
      result_seq.len() == max_len + 1,
      // Partial result is valid bit string up to i
      forall |j: int| 0 <= j && j <= i ==> (result_seq.index((max_len - i) + j) == '0' || result_seq.index((max_len - i) + j) == '1'),
  {
    let digit1 = if i < l1 && s1.index(l1 - 1 - i) == '1' { 1 nat } else { 0 nat };
    let digit2 = if i < l2 && s2.index(l2 - 1 - i) == '1' { 1 nat } else { 0 nat };

    let sum = digit1 + digit2 + carry;
    carry = sum / 2;
    let current_digit = sum % 2;

    result_seq = result_seq.update( (max_len - i) as int, if current_digit == 1 { '1' } else { '0' });

    i = i + 1;
  }

  // Handle final carry
  result_seq = result_seq.update(0, if carry == 1 { '1' } else { '0' });

  // Remove leading zero if not the only digit
  if result_seq.index(0) == '0' && result_seq.len() > 1 {
    result_seq.subrange(1, result_seq.len() as int)
  } else {
    result_seq
  }
} */

spec fn helper_add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    ValidBitString(result),
{
  let l1 = s1.len();
  let l2 = s2.len();
  let max_len = if l1 > l2 { l1 } else { l2 };

  let mut result_seq = new_str_repr_seq(max_len + 1);
  let mut carry = 0 nat;

  let mut i = 0 nat;
  while i < max_len
    invariant
      0 <= i,
      i <= max_len,
      carry == 0 || carry == 1,
      result_seq.len() == max_len + 1,
      forall |j: int| 0 <= j && j < i ==> (
        result_seq.index((max_len - j) as int) == '0' || result_seq.index((max_len - j) as int) == '1'
      ),
  decreases max_len - i
  {
    let digit1 = if (i < l1) && s1.index((l1 - 1 - i) as int) == '1' { 1 nat } else { 0 nat };
    let digit2 = if (i < l2) && s2.index((l2 - 1 - i) as int) == '1' { 1 nat } else { 0 nat };

    let sum = digit1 + digit2 + carry;
    carry = sum / 2;
    let current_digit = sum % 2;

    result_seq = result_seq.update( (max_len - i) as int, if current_digit == 1 { '1' } else { '0' });

    i = i + 1;
  }

  // Handle final carry
  result_seq = result_seq.update(0, if carry == 1 { '1' } else { '0' });
  
  if result_seq.index(0) == '0' && result_seq.len() > 1 {
    result_seq.subrange(1, result_seq.len() as int)
  } else {
    result_seq
  }
}

spec fn new_str_repr_seq(len: nat) -> Seq<char>
  ensures (new_str_repr_seq(len).len() == len)
{
  Seq::new(len, |i:int| '0')
}

proof fn u32_to_char_digits(x: nat) -> (s: Seq<char>)
  requires x < 2
  ensures (
    s.len() == 1
    && (
      (x == 0 && s.index(0) == '0')
      ||
      (x == 1 && s.index(0) == '1')
    )
  )
{
  if x == 0 {
    let s_local = Seq::new(1, |i:int| '0');
    s_local
  } else {
    let s_local = Seq::new(1, |i:int| '1');
    s_local
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed types and indexing for vector operations. */
{
  let s1 = a@;
  let s2 = b@;

  let result_seq = helper_add_bit_strings(s1, s2);

  let mut result_vec: Vec<char> = Vec::<char>::new();
  let mut i: nat = 0;
  while i < result_seq.len()
    invariant
      0 <= i,
      i <= result_seq.len(),
      result_vec.len() == i,
      forall |j: int| 0 <= j && j < i ==> result_vec.index(j) == result_seq.index(j),
  {
    result_vec.push(result_seq.index(i as int));
    i = i + 1;
  }

  result_vec
}
// </vc-code>

fn main() {}
}

