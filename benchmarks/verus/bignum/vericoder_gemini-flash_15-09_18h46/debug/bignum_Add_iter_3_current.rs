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
/* helper modified by LLM (iteration 3): Removed unneeded helper function `AddInt`. */
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation errors related to `nat` suffix, mismatched types, and indexing into sequences. Conversions to `int` are made where necessary. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0; // Fixed: type `nat` for `carry`
    let len1: int = s1.len() as int;
    let len2: int = s2.len() as int;
    let max_len: int = if len1 > len2 { len1 } else { len2 };
    let mut i: int = 0; // Fixed: type `int` for `i`

    while i < max_len || carry > 0
        invariant
            i >= 0,
            carry == 0 || carry == 1,
            result_vec@.len() == i as int,
            forall |j: int| 0 <= j && j < result_vec@.len() ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
            // Str2Int(result_vec@) + carry * (1 << i as int) == 
            //     (if i < len1 { Str2Int(s1@.subrange(len1 - i, len1)) } else { 0nat }) + 
            //     (if i < len2 { Str2Int(s2@.subrange(len2 - i, len2)) } else { 0nat }),
        decreases max_len - i
    {
        let bit1 = if i < len1 && s1@[(len1 - 1 - i) as int] == '1' { 1 } else { 0 }; // Fixed: `nat` suffix removed, index type conversion, literal type
        let bit2 = if i < len2 && s2@[(len2 - 1 - i) as int] == '1' { 1 } else { 0 }; // Fixed: `nat` suffix removed, index type conversion, literal type

        let sum_bits: nat = (bit1 + bit2 + carry) as nat;
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