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
/* helper modified by LLM (iteration 7): Fixed type annotation, `snoc` method, and `nat` type conversion issues. */
spec fn SubHelper(s1: Seq<char>, s2: Seq<char>, carry_in: int) -> (res: (Seq<char>, int))
  requires
    s1.len() == s2.len(),
    s1.len() >= 0,
    ValidBitString(s1),
    ValidBitString(s2),
    carry_in == 0 || carry_in == 1,
    Str2Int(s1) as int - Str2Int(s2) as int - carry_in >= 0
  decreases s1.len()
{
  if s1.len() == 0 {
    (Seq::<char>::empty(), 0)
  } else {
    let s1_last = s1.index(s1.len() as int - 1);
    let s2_last = s2.index(s2.len() as int - 1);

    let digit1: int = if s1_last == '1' { 1 } else { 0 };
    let digit2: int = if s2_last == '1' { 1 } else { 0 };

    let current_diff = digit1 - digit2 - carry_in;

    let result_digit = if current_diff >= 0 { current_diff } else { current_diff + 2 };
    let updated_new_carry = if current_diff >= 0 { 0 } else { 1 };
      
    let result_char = if result_digit == 1 { '1' } else { '0' };

    let (prev_res_seq, _) = SubHelper(
      s1.subrange(0, s1.len() as int - 1),
      s2.subrange(0, s2.len() as int - 1),
      updated_new_carry
    );

    (prev_res_seq.push(result_char), updated_new_carry)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Add leading zero handling for `Str2Int` and fixed `nat` comparison. */
{
    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() == 0 && s2_seq.len() == 0 {
        let mut res_vec = Vec::new();
        res_vec.push('0');
        return res_vec;
    }

    let max_len = if s1_seq.len() >= s2_seq.len() { s1_seq.len() } else { s2_seq.len() };
    
    let s1_padded = Seq::new(max_len, |i| if i < max_len - s1_seq.len() { '0' } else { s1_seq.index(i - (max_len - s1_seq.len())) });
    let s2_padded = Seq::new(max_len, |i| if i < max_len - s2_seq.len() { '0' } else { s2_seq.index(i - (max_len - s2_seq.len())) });

    let mut result_vec = Vec::new();
    let mut carry = 0;
    let mut i = max_len - 1;

    while i >= 0 
        invariant
            0 <= i + 1 <= max_len,
            result_vec.len() == max_len - (i + 1),
            carry == 0 || carry == 1,
            ValidBitString(result_vec@),
    {
        let digit1: int = if s1_padded.index(i) == '1' { 1 } else { 0 };
        let digit2: int = if s2_padded.index(i) == '1' { 1 } else { 0 };

        let current_diff = digit1 - digit2 - carry;

        let result_digit = if current_diff >= 0 { current_diff } else { current_diff + 2 };
        carry = if current_diff >= 0 { 0 } else { 1 };

        result_vec.insert(0, if result_digit == 1 { '1' } else { '0' });

        i = i - 1;
    }

    while result_vec.len() > 1 && result_vec.index(0) == '0' {
        result_vec.remove(0);
    }

    result_vec
}
// </vc-code>

fn main() {}
}


