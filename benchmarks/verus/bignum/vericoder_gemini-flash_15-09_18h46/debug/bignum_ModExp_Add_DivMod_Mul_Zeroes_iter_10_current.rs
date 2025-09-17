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
/* helper modified by LLM (iteration 10): Removed compilation error. */
spec fn new_str_repr_seq(len: nat) -> Seq<char>
  ensures result.len() == len,
          forall |i: int| 0 <= i && i < len ==> result.index(i) == '0'
{
  Seq::new(len as int, |i: int| '0')
}

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

  let mut result_seq = new_str_repr_seq((max_len + 1) as nat);
  let mut carry: nat = 0;

  let mut i: nat = 0;
  while i < max_len
    invariant
      0 <= i,
      i <= max_len,
      carry == 0 || carry == 1,
      result_seq.len() == (max_len + 1) as nat,
      forall |j: int| (0 <= j && j < i as int) ==> ((result_seq.index(j) == '0') || (result_seq.index(j) == '1')),
      ValidBitString(result_seq.subrange(0 as int, i as int)),
      i as int <= result_seq.len(),
  decreases max_len - i
  {
    let digit1: nat = if (i < l1) && s1.index((l1 - 1 - i) as int) == '1' { 1 } else { 0 };
    let digit2: nat = if (i < l2) && s2.index((l2 - 1 - i) as int) == '1' { 1 } else { 0 };

    let sum = digit1 + digit2 + carry;
    carry = sum / 2;
    let current_digit = sum % 2;

    result_seq = result_seq.update( (max_len - i) as int, if current_digit == 1 { '1' } else { '0' });

    i = i + 1;
  }

  let final_result_seq = result_seq.update(0, if carry == 1 { '1' } else { '0' });
  
  if final_result_seq.index(0) == '0' && final_result_seq.len() > 1 && max_len > 0 {
    final_result_seq.subrange(1, final_result_seq.len() as int)
  } else {
    final_result_seq
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type error `result_seq.index(i as int)` */
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

