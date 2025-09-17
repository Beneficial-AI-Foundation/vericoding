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
/* helper modified by LLM (iteration 3): Adjusted target_len to be `int` internally for calculation, then cast back to `nat` for `Seq::fill` and `add` to satisfy type constraints. */
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
    Seq::fill(diff_int as nat, |idx| '0').add(s)
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
/* code modified by LLM (iteration 3): Fixed type casting errors by introducing `ghost` variables for `nat` conversions. */
{
    let mut result: Vec<char> = Vec::new();
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let padded_len = (max_len + 1);

    let ghost padded_len_nat = padded_len as nat;

    let s1_padded_seq = normalize_length_and_pad(s1@, padded_len_nat);
    let s2_padded_seq = normalize_length_and_pad(s2@, padded_len_nat);

    let mut carry: nat = 0;
    let mut i: int = (padded_len - 1);

    while i >= 0
        invariant
            0 <= i + 1 && i + 1 <= padded_len as int,
            carry == 0 || carry == 1,
            result.len() == (padded_len_nat - (i + 1) as nat),
            ValidBitString(result@),
    {
        let ghost bit1 = if s1_padded_seq.index(i) == '1' { 1nat } else { 0nat };
        let ghost bit2 = if s2_padded_seq.index(i) == '1' { 1nat } else { 0nat };

        let ghost sum_bits = bit1 + bit2 + carry;

        let current_bit = if sum_bits % 2 == 1 { '1' } else { '0' };
        carry = sum_bits / 2;

        result.insert(0, current_bit);
        i = i - 1;
    }

    if carry == 1 {
        result.insert(0, '1');
    }

    let mut first_digit_idx = 0;
    while first_digit_idx < result.len() - 1 && result.index(first_digit_idx) == '0' {
        first_digit_idx = first_digit_idx + 1;
    }

    let ghost first_digit_idx_nat = first_digit_idx as nat;
    let ghost result_len_nat = result.len() as nat;

    let final_result_vec = result.subslice(first_digit_idx_nat, (result_len_nat - first_digit_idx_nat));

    Vec::from_seq(final_result_vec@)
}
// </vc-code>

fn main() {}
}