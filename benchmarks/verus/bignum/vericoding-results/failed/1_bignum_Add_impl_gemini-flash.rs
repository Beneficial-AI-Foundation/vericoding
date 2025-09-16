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

// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed compiler errors involving `nat` literals and updated loop condition to match `max_len` correctly. Removed `assume(false)` to enable actual verification. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0;
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    let max_len: usize = if len1 > len2 { len1 } else { len2 };
    let mut i: usize = 0;

    while (i < max_len) || (carry > 0)
        invariant
            i <= max_len + 1,
            carry == 0 || carry == 1,
            result_vec@.len() == i as nat,
            forall |j: int| 0 <= j && j < result_vec@.len() ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
        decreases max_len + 1 - i
    {
        let bit1: nat = if i < len1 && s1[len1 - 1 - i] == '1' { 1 } else { 0 };
        let bit2: nat = if i < len2 && s2[len2 - 1 - i] == '1' { 1 } else { 0 };

        let sum_bits: nat = bit1 + bit2 + carry;
        let current_bit: nat = sum_bits % 2;
        carry = sum_bits / 2;

        result_vec.insert(0, if current_bit == 1 { '1' } else { '0' });
        i = i + 1;
    }

    if result_vec.is_empty() {
        result_vec.insert(0, '0');
    }
    result_vec
}
// </vc-code>

fn main() {}
}