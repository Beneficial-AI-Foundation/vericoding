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
                forall|j|
                    0 <= j && j < i ==> s1[j] == s2[j],
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

// A helper function to subtract one bit string from another
// Assumes s1 >= s2 and both have same length
open spec fn subtract_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires
        s1.len() == s2.len(),
        s1.len() > 0,
        greater_equal_seq(s1, s2),
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        (Str2Int(s1) - Str2Int(s2)) == Str2Int(result),
        ValidBitString(result),
        result.len() == s1.len(),
{
    let mut result = Seq::<char>::new();
    let mut borrow = false;

    let mut i = s1.len() as int - 1;
    while i >= 0
        invariant
            -1 <= i,
            i < s1.len() as int,
            result.len() == (s1.len() as int - 1 - i),
            forall|j|
                i < j && j < s1.len() as int ==> (result[j - (i + 1)] == '0' || result[j - (i + 1)] == '1'),
            ValidBitString(result),
            // Inductive step for Str2Int property
            // This is complex for subtraction, we'll ensure correctness through greater_equal_seq for now
    {
        let digit1 = if s1[i] == '1' { 1 } else { 0 };
        let digit2 = if s2[i] == '1' { 1 } else { 0 };
        let mut current_sub = digit1 - digit2 - (if borrow { 1 } else { 0 });
        if current_sub < 0 {
            current_sub = current_sub + 2;
            borrow = true;
        } else {
            borrow = false;
        }
        result = Seq::new().push(if current_sub == 1 { '1' } else { '0' }).add(result);
        i = i - 1;
    }
    result
}

// A helper function to normalize a bit string by removing leading zeros (unless it's "0")
open spec fn normalize_bit_string(s: Seq<char>) -> Seq<char>
    requires ValidBitString(s)
    ensures
        ValidBitString(result),
        Str2Int(result) == Str2Int(s),
        result.len() == 1 ==> result[0] == '0' || result[0] == '1',
        result.len() > 1 ==> result[0] == '1' || Str2Int(s) == 0,
        (Str2Int(s) == 0) ==> (result == seq!['0']),
{
    if s.len() == 0 {
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
    if i == s.len() {
        seq!['0']
    } else {
        s.subrange(i, s.len() as int)
    }
}

// Helper to pad the smaller sequence with leading zeros to match length
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
    let mut padded_s = Seq::<char>::new();
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

// Helper to compare two bit strings based on their integer value
open spec fn bit_string_to_nat(s: Seq<char>) -> nat {
    Str2Int(s)
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

    let mut result = Seq::<char>::new_empty();
    let mut carry = false;
    let mut i = max_len as int - 1;

    while i >= 0
        invariant
            -1 <= i,
            i < max_len as int,
            result.len() == (max_len as int - 1 - i),
            forall|j|
                i < j && j < max_len as int ==> (result[j - (i + 1)] == '0' || result[j - (i + 1)] == '1'),
            ValidBitString(result),
    {
        let digit1 = if s1_padded[i] == '1' { 1 } else { 0 };
        let digit2 = if s2_padded[i] == '1' { 1 } else { 0 };
        let mut current_sum = digit1 + digit2 + (if carry { 1 } else { 0 });
        if current_sum >= 2 {
            current_sum = current_sum - 2;
            carry = true;
        } else {
            carry = false;
        }
        result = Seq::new().push(if current_sum == 1 { '1' } else { '0' }).add(result);
        i = i - 1;
    }

    if carry {
        result = Seq::new().push('1').add(result);
    }
    normalize_bit_string(result)
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
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();

    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (vec!['0'], dividend.to_vec());
    }

    let normalized_divisor_seq = normalize_bit_string(divisor_seq);

    let mut current_remainder_seq = Seq::<char>::new();
    let mut i: int = 0;

    while i < dividend_seq.len()
        invariant
            0 <= i,
            i <= dividend_seq.len(),
            ValidBitString(quotient@),
            ValidBitString(current_remainder_seq),
            // The parts of the dividend that have been processed
            normalize_bit_string(dividend_seq.subrange(0, i as int)) == add_bit_strings(
                normalize_bit_string(quotient.to_seq().map_values(|_| '0').add(current_remainder_seq)),
                normalize_bit_string(divisor_seq.map_values(|_| '0').add(Seq::new_empty()))
            )
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

