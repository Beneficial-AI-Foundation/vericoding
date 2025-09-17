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
/* helper modified by LLM (iteration 4): Fixed Seq::fill compilation error to Seq::new */
spec fn normalize_length_and_pad(s: Seq<char>, target_len: nat) -> Seq<char>
  ensures
    normalize_length_and_pad(s, target_len).len() == target_len,
    forall |i: int| #![auto] 0 <= i && i < target_len as int - s.len() ==> normalize_length_and_pad(s, target_len).index(i) == '0',
    forall |i: int| #![auto] 0 <= i && i < s.len() ==> normalize_length_and_pad(s, target_len).index(i + (target_len as int - s.len()) as int) == s.index(i),
    ValidBitString(s) ==> ValidBitString(normalize_length_and_pad(s, target_len))
{
  let diff_int = (target_len as int) - (s.len() as int);
  if diff_int <= 0 {
    s
  } else {
    let padding = Seq::new(diff_int as nat, |idx| '0');
    padding.add(s)
  }
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
/* code modified by LLM (iteration 4): Fixed all remaining type mismatch errors and compilation errors, including `Seq::fill` and `Vec::subslice`. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let padded_len: usize = (max_len + 1);

    let ghost padded_len_nat = padded_len as nat;

    let s1_padded_seq = normalize_length_and_pad(s1@, padded_len_nat);
    let s2_padded_seq = normalize_length_and_pad(s2@, padded_len_nat);

    let mut carry: nat = 0;
    let mut i: int = (padded_len as int - 1);

    while i >= 0
        invariant
            0 <= i + 1 && i + 1 <= padded_len as int,
            (carry == 0 || carry == 1) ,
            result_vec.len() == (padded_len as nat - (i as nat + 1)) ,
            ValidBitString(result_vec@),
    {
        let bit1 = if s1_padded_seq.index(i) == '1' { 1nat } else { 0nat };
        let bit2 = if s2_padded_seq.index(i) == '1' { 1nat } else { 0nat };

        let sum_bits = bit1 + bit2 + carry;

        let current_bit = if sum_bits % 2 == 1 { '1' } else { '0' };
        carry = sum_bits / 2;

        result_vec.insert(0, current_bit);
        i = i - 1;
    }

    if carry == 1 {
        result_vec.insert(0, '1');
    }

    let mut first_digit_idx: usize = 0;
    while first_digit_idx < result_vec.len() - 1 && result_vec[first_digit_idx] == '0'
        invariant
            first_digit_idx < result_vec.len()
    {
        first_digit_idx = first_digit_idx + 1;
    }

    let final_result_seq = result_vec@.subrange(first_digit_idx as int, result_vec.len() as int);

    Vec::from_iter(final_result_seq.iter())
}
// </vc-code>

fn main() {}
}