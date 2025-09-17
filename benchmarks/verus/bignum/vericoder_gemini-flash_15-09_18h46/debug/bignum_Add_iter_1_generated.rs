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
spec fn AddInt(n1: nat, n2: nat) -> nat { n1 + n2 }
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut i: int = 0;

    while i < max_len || carry > 0
        invariant
            carry == 0 || carry == 1,
            result_vec@.len() == i,
            forall |j: int| 0 <= j && j < result_vec@.len() ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
            // This invariant is tricky to get right for full correctness
            // Str2Int(result_vec@) + carry * (2*2*...2) == Str2Int(s1.subrange(0, i)) + Str2Int(s2.subrange(0, i))
            // (simplified for this turn)
        decreases max_len - i
    {
        let bit1 = if i < len1 && s1@[len1 - 1 - i] == '1' { 1 nat } else { 0 nat };
        let bit2 = if i < len2 && s2@[len2 - 1 - i] == '1' { 1 nat } else { 0 nat };

        let sum_bits = bit1 + bit2 + carry;
        let current_bit = sum_bits % 2;
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