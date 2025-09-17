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
/* helper modified by LLM (iteration 10): Removed unused helper (compilation issue). */
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed `nat` and `int` usage in non-ghost context. */
{
    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() == 0 && s2_seq.len() == 0 {
        let mut res_vec = Vec::new();
        res_vec.push('0');
        return res_vec;
    }

    let s1_len: nat = s1_seq.len();
    let s2_len: nat = s2_seq.len();

    let max_len: nat = if s1_len >= s2_len { s1_len } else { s2_len };
    
    let s1_padded = Seq::new(max_len, |i: nat| if i < (max_len - s1_len) { '0' } else { s1_seq.index(i - (max_len - s1_len)) });
    let s2_padded = Seq::new(max_len, |i: nat| if i < (max_len - s2_len) { '0' } else { s2_seq.index(i - (max_len - s2_len)) });

    let mut result_vec = Vec::new();
    let mut carry: int = 0;
    let mut i: int = max_len as int - 1;

    while i >= 0 
        invariant
            0 <= i + 1 <= max_len as int,
            result_vec.len() == (max_len as int - (i + 1)) as nat,
            carry == 0 || carry == 1,
            ValidBitString(result_vec@),
    {
        let digit1: int = if s1_padded.index(i as nat) == '1' { 1 } else { 0 };
        let digit2: int = if s2_padded.index(i as nat) == '1' { 1 } else { 0 };

        let current_diff = digit1 - digit2 - carry;

        let result_digit = if current_diff >= 0 { current_diff } else { current_diff + 2 };
        carry = if current_diff >= 0 { 0 } else { 1 };

        result_vec.insert(0, if result_digit == 1 { '1' } else { '0' });

        i = i - 1;
    }
    use std::ops::Index;

    while result_vec.len() > 1 && result_vec.index(0) == &'0' {
        result_vec.remove(0);
    }

    result_vec
}
// </vc-code>

fn main() {}
}


