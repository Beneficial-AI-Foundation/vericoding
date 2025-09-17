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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes needed for helper, but added comment to satisfy prompt. */
spec fn pad_left(s_old: Seq<char>, desired_len: int) -> Seq<char>
  requires
    desired_len >= s_old.len(),
    desired_len >= 0,
  ensures
    pad_left(s_old, desired_len).len() == desired_len,
    forall |i: int| #![auto]
      s_old.len() <= i && i < desired_len ==> (pad_left(s_old, desired_len).index(i) == '0'),
    forall |i: int| #![auto]
      0 <= i && i < s_old.len() ==> (pad_left(s_old, desired_len).index(i) == s_old.index(i))
{
  let diff = (desired_len - s_old.len());
  Seq::new(desired_len, |i: int| {
    if i < diff { '0' } else { s_old.index(i - diff) }
  })
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected types for `len1` and `len2` to be `usize` to resolve compilation errors. */
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 > len2 { len1 } else { len2 };

  let s1_padded = pad_left(s1@, max_len as int);
  let s2_padded = pad_left(s2@, max_len as int);

  let mut result: Vec<char> = Vec::new();
  let mut carry: nat = 0nat;

  let mut i: usize = 0;
  while i < max_len
    invariant
      0 <= i as int <= max_len as int,
      carry == 0 || carry == 1,
      result.len() == i,
      forall |j: int| 0 <= j < i as int ==> (result@[j] == '0' || result@[j] == '1'),
      (
        (Str2Int(result@) + carry * (1nat << i as nat))
         == (Str2Int(s1_padded.drop_last(max_len as int - i as int)) + Str2Int(s2_padded.drop_last(max_len as int - i as int)))
      )
  {
    let bit1 = if s1_padded.index(max_len as int - 1 - i as int) == '1' { 1nat } else { 0nat };
    let bit2 = if s2_padded.index(max_len as int - 1 - i as int) == '1' { 1nat } else { 0nat };
    
    let sum = bit1 + bit2 + carry;
    
    let current_bit = if sum % 2 == 1 { '1' } else { '0' };
    carry = sum / 2;
    
    result.push(current_bit);

    i = i + 1;
  }

  if carry == 1nat {
    result.push('1');
  }

  result.reverse();
  result
}
// </vc-code>

fn main() {}
}