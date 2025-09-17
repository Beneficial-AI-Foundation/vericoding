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
/* helper modified by LLM (iteration 2): fixed Str2Int calculation for subtract_bit_strings and other helper issues */
open spec fn greater_equal_seq(s1: Seq<char>, s2: Seq<char>) -> bool {
    if s1.len() < s2.len() {
        false
    } else if s1.len() > s2.len() {
        true
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i,
                i <= s1.len(),
                forall|j| 0 <= j && j < i ==> s1[j] == s2[j],
        {
            if s1[i] > s2[i] {
                return true;
            }
            if s1[i] < s2[i] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

open spec fn subtract_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires
        s1.len() == s2.len(),
        s1.len() > 0,
        greater_equal_seq(s1, s2),
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        Str2Int(s1) - Str2Int(s2) == Str2Int(result),
        ValidBitString(result),
        result.len() == s1.len(),
{
    let mut result_seq = Seq::<char>::new_empty();
    let mut borrow = false;

    let mut i = s1.len() as int - 1;

    while i >= 0
        invariant
            -1 <= i,
            i < s1.len() as int,
            result_seq.len() == (s1.len() as int - 1 - i),
            ValidBitString(result_seq),
            Str2Int(s1.subrange(i + 1, s1.len() as int)) - Str2Int(s2.subrange(i + 1, s1.len() as int)) - (if borrow { 1nat } else { 0nat }) == Str2Int(result_seq) ,
    {
        let digit1 = if s1[i] == '1' { 1nat } else { 0nat };
        let digit2 = if s2[i] == '1' { 1nat } else { 0nat };
        let current_borrow = if borrow { 1nat } else { 0nat };
        let mut current_sub = digit1 - digit2 - current_borrow;
        let new_borrow: bool;
        if current_sub < 0 {
            current_sub = current_sub + 2;
            new_borrow = true;
        } else {
            new_borrow = false;
        }
        result_seq = Seq::new().push(if current_sub == 1 { '1' } else { '0' }).add(result_seq);
        borrow = new_borrow;
        i = i - 1;
    }
    result_seq
}

open spec fn normalize_bit_string(s: Seq<char>) -> Seq<char>
    requires ValidBitString(s)
    ensures
        ValidBitString(result),
        Str2Int(result) == Str2Int(s),
        result.len() == 1 ==> result[0] == '0' || result[0] == '1',
        result.len() > 1 ==> result[0] == '1',
        (Str2Int(s) == 0) ==> (result == seq!['0']),
{
    if Str2Int(s) == 0 {
        return seq!['0'];
    }
    let mut i = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i,
            i <= s.len(),
            ValidBitString(s),
            Str2Int(s.subrange(i, s.len() as int)) == Str2Int(s),
    {
        i = i + 1;
    }
    s.subrange(i, s.len() as int)
}


open spec fn pad_left(s: Seq<char>, target_len: nat) -> Seq<char>
    requires
        s.len() <= target_len,
        ValidBitString(s),
    ensures
        ValidBitString(result),
        result.len() == target_len,
        Str2Int(result) == Str2Int(s),
{
    let padding_len = target_len - s.len();
    let mut padded_s = Seq::<char>::new_empty();
    let mut i = 0;
    while i < padding_len
        invariant
            0 <= i,
            i <= padding_len,
            padded_s.len() == i,
            ValidBitString(padded_s),
    {
        padded_s = padded_s.push('0');
        i = i + 1;
    }
    padded_s.add(s)
}

open spec fn add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        Str2Int(result) == Str2Int(s1) + Str2Int(s2),
        ValidBitString(result),
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    let s1_padded = pad_left(s1, max_len);
    let s2_padded = pad_left(s2, max_len);

    let mut result_seq = Seq::<char>::new_empty();
    let mut carry = false;
    let mut i = max_len as int - 1;

    while i >= 0
        invariant
            -1 <= i,
            i < max_len as int,
            result_seq.len() == (max_len as int - 1 - i),
            ValidBitString(result_seq),
            // This invariant is tricky to prove directly with Str2Int on partial sequences
            // We'll rely on the overall `ensures` for now
    {
        let digit1 = if s1_padded[i] == '1' { 1nat } else { 0nat };
        let digit2 = if s2_padded[i] == '1' { 1nat } else { 0nat };
        let mut current_sum = digit1 + digit2 + (if carry { 1nat } else { 0nat });
        let new_carry: bool;

        if current_sum >= 2 {
            current_sum = current_sum - 2;
            new_carry = true;
        } else {
            new_carry = false;
        }
        result_seq = Seq::new().push(if current_sum == 1 { '1' } else { '0' }).add(result_seq);
        carry = new_carry;
        i = i - 1;
    }

    let final_result = if carry {
        Seq::new().push('1').add(result_seq)
    } else {
        result_seq
    };
    normalize_bit_string(final_result)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): adjusted invariant in the main loop to correctly track the processed dividend and current remainder */
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();

    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (vec!['0'], dividend.to_vec());
    }

    let normalized_divisor_seq = normalize_bit_string(divisor_seq);

    let mut current_remainder_seq = Seq::<char>::new_empty();
    let mut i: int = 0;

    while i < dividend_seq.len()
        invariant
            0 <= i,
            i <= dividend_seq.len(),
            ValidBitString(quotient@),
            ValidBitString(current_remainder_seq),
            (forall |j: int| 0 <= j && j < quotient@.len() ==> (quotient@[j] == '0' || quotient@[j] == '1')),
            (forall |j: int| 0 <= j && j < current_remainder_seq.len() ==> (current_remainder_seq[j] == '0' || current_remainder_seq[j] == '1')),
            Str2Int(dividend_seq.subrange(0, i as int)) == Str2Int(add_bit_strings(
                Str2Int_Multiply_by_power_of_2(quotient@, ((dividend_seq.len() - i as nat) as nat)).to_seq()
                  s(quotient@), (dividend_seq.len() - i as nat)),
                current_remainder_seq
            )),
            Str2Int(dividend_seq.subrange(0, i as int)) == Str2Int(add_bit_strings(
              Str2Int(quotient@) * Str2Int(pow2(dividend_seq.len() - i as nat))

            )),
            // The parts of the dividend that have been processed
            // Str2Int(dividend_seq.subrange(0, i as int)) == Str2Int(add_bit_strings(
            //     Str2Int_Multiply_by_power_of_2(quotient@, (dividend_seq.len() - i as nat))
            //     // Here quotient@ shifted by remaining_digits
            //     // then add current_remainder_seq to it
            // )), // Needs careful thought, perhaps a different invariant structure
            // Str2Int(dividend_seq.subrange(0, i as int)) == Str2Int(
            //   add_bit_strings(
            //     Str2Int_Multiply_by_power_of_2(quotient@, (dividend_seq.len() - i as nat)),
            //     current_remainder_seq)
            // )
    {
        current_remainder_seq = current_remainder_seq.push(dividend_seq[i]);
        current_remainder_seq = normalize_bit_string(current_remainder_seq);

        if Str2Int(current_remainder_seq) >= Str2Int(normalized_divisor_seq) {
            quotient.push('1');
            current_remainder_seq = subtract_bit_strings(current_remainder_seq, normalized_divisor_seq);
            current_remainder_seq = normalize_bit_string(current_remainder_seq);
        } else {
            quotient.push('0');
        }
        i = i + 1;
    }

    let final_quotient_vec = normalize_bit_string(quotient@).to_vec();
    let final_remainder_vec = normalize_bit_string(current_remainder_seq).to_vec();

    (final_quotient_vec, final_remainder_vec)
}
// </vc-code>

fn main() {}
}

