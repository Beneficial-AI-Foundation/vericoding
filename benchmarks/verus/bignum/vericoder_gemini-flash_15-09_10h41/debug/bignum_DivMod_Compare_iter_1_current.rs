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
spec fn Subtract_BitString(A: Seq<char>, B: Seq<char>) -> Seq<char>
  requires ValidBitString(A), ValidBitString(B), A.len() == B.len(), Str2Int(A) >= Str2Int(B)
  ensures ValidBitString(result()), result().len() == A.len(), Str2Int(result()) == Str2Int(A) - Str2Int(B)
  decreases A.len()
{
  if A.len() == 0 {
    seq![]
  } else {
    let a_last = (if A.index(A.len() as int - 1) == '1' { 1 } else { 0 });
    let b_last = (if B.index(B.len() as int - 1) == '1' { 1 } else { 0 });
    if a_last >= b_last {
      let sub_res = Subtract_BitString(A.subrange(0, A.len() as int - 1), B.subrange(0, B.len() as int - 1));
      sub_res.push_back(if a_last - b_last == 1 { '1' } else { '0' })
    } else {
      // Borrow from the next bit
      let A_prefix_prime = Subtract_BitString(A.subrange(0, A.len() as int - 1), seq![_ in 0..A.len() as int - 1 => '0'].update(A.len() as int - 2, '1'));
      let B_prefix = B.subrange(0, B.len() as int - 1);
      let sub_res = Subtract_BitString(A_prefix_prime, B_prefix);
      sub_res.push_back(if a_last + 2 - b_last == 1 { '1' } else { '0' })
    }
  }
}

spec fn PrependZeros(s: Seq<char>, count: nat) -> Seq<char>
  ensures ValidBitString(result()), result().len() == s.len() + count, Str2Int(result()) == Str2Int(s)
{
  seq![_ in 0..count => '0'] + s
}

spec fn PadToLength(s: Seq<char>, len: nat) -> Seq<char>
  ensures ValidBitString(result()), result().len() == len, Str2Int(result()) == Str2Int(s)
{
  if s.len() < len {
    PrependZeros(s, len - s.len())
  } else {
    s
  }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let d_len = dividend.len();
  let r_len = divisor.len();

  let mut remainder = dividend.to_vec();
  let mut quotient = Vec::<char>::new();

  while quotient.len() < d_len
    invariant
      remainder.len() == d_len,
      quotient.len() <= d_len,
      ValidBitString(remainder@),
      ValidBitString(quotient@),
      Str2Int(dividend@) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@),
      forall |i: int| 0 <= i && i < quotient.len() ==> (quotient@[i] == '0' || quotient@[i] == '1')
  {
    let current_idx = quotient.len();
    let mut term_to_subtract: Seq<char>;

    if current_idx + r_len <= d_len {
      // Consider the segment `remainder[current_idx..current_idx+r_len]`
      let segment = remainder@[current_idx..current_idx+r_len];

      if Str2Int(segment) >= Str2Int(divisor@) {
        quotient.push('1');
        term_to_subtract = PadToLength(divisor@, r_len);
      } else {
        quotient.push('0');
        term_to_subtract = PadToLength(seq![], r_len); // Effectively subtract 0
      }
    } else {
      // The remaining part is shorter than divisor, so append '0's to quotient and the remainder stays as is
      quotient.push('0');
      term_to_subtract = PadToLength(seq![], r_len); // This won't actually be subtracted in the final iteration
    }

    if quotient.len() > current_idx {
      // Apply subtraction only if a digit was added to quotient (i.e., not just a padding step)
      let sub_amount = term_to_subtract;

      let mut new_remainder_seq = remainder@;
      let mut carry_out = 0;

      proof {
        if current_idx + r_len <= d_len {
          assert(sub_amount.len() == r_len);
          assert(new_remainder_seq.subrange(current_idx, current_idx + r_len).len() == r_len);
        }
      }

      if current_idx + r_len <= d_len {
        // Perform binary subtraction on the relevant segment
        let segment_to_subtract_from = new_remainder_seq.subrange(current_idx, current_idx + r_len);

        let sub_result = Subtract_BitString(segment_to_subtract_from, sub_amount);

        for i in 0..r_len as int {
          new_remainder_seq = new_remainder_seq.update(current_idx + i, sub_result.index(i));
        }
      }
      remainder = new_remainder_seq.to_vec();
    }
  }

  // Trim leading zeros from the final quotient and remainder
  let mut final_quotient_vec = Vec::<char>::new_with(quotient.len(), |i| quotient.vec_index(i));
  let mut first_one_q = 0;
  while first_one_q < final_quotient_vec.len() && final_quotient_vec[first_one_q] == '0' {
    first_one_q = first_one_q + 1;
  }
  let final_quotient = if first_one_q == final_quotient_vec.len() { vec!['0'] } else { final_quotient_vec.subslice(first_one_q, final_quotient_vec.len()).to_vec() };

  let mut final_remainder_vec = Vec::<char>::new_with(remainder.len(), |i| remainder.vec_index(i));
  let mut first_one_r = 0;
  while first_one_r < final_remainder_vec.len() && final_remainder_vec[first_one_r] == '0' {
    first_one_r = first_one_r + 1;
  }
  let final_remainder = if first_one_r == final_remainder_vec.len() { vec!['0'] } else { final_remainder_vec.subslice(first_one_r, final_remainder_vec.len()).to_vec() };

  (final_quotient, final_remainder)
}
// </vc-code>

fn main() {}
}

