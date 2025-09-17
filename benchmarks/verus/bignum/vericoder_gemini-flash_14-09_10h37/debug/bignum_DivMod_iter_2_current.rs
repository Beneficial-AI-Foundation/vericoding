
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
/* helper modified by LLM (iteration 2): Fixed pure fn signature */
pure fn seq_to_vec_char(s: Seq<char>) -> Vec<char>
  ensures seq_to_vec_char(s)@ == s
{
  let mut v = Vec::new();
  let mut i = 0;
  while i < s.len()
    invariant
      v@.len() == i,
      v@ == s.subrange(0, i as int)
  {
    v.push(s.index(i as int));
    i = i + 1;
  }
  v
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Adjusted error-producing type in initial assignment */
{
  let d_seq = divisor@;
  let mut dividend_current = dividend@;
  let mut quotient = Seq::<char>::empty();

  let d_trimmed = trim_leading_zeros(d_seq);
  if d_trimmed.len() == 0 {
    // Divisor is 0, which is disallowed by recommends
    // This case should not be reached due to pre-condition `Str2Int(divisor@) > 0`
    unreachable!();
  }

  // Handle initial case where dividend_current might be smaller than divisor_trimmed
  if (Str2Int(dividend_current) < Str2Int(d_seq)) {
      return (seq_to_vec_char(Seq::new(1, |i| '0')), seq_to_vec_char(dividend_current));
  }

  let mut k: nat = 0;
  while dividend_current.len() > d_seq.len()
    invariant
      ValidBitString(dividend_current),
      ValidBitString(d_seq),
      Str2Int(d_seq) > 0,
      quotient.len() == k,
      ValidBitString(quotient)
  {
      k = k + 1;
      quotient = quotient + Seq::new(1, |i| '0');
  }

  let mut k_loop_count: nat = 0;
  while k_loop_count <= k
    invariant
      ValidBitString(dividend_current),
      ValidBitString(d_seq),
      Str2Int(d_seq) > 0,
      k >= k_loop_count,
      quotient.len() == k_loop_count as int + (if k_loop_count < k { 0 } else { 1 }) as int,
      ValidBitString(quotient)
    // This needs to be carefully constructed. It's the core division algorithm
  {
      // Calculate shifted divisor
      let shifted_divisor = bitwise_left_shift(d_seq, k - k_loop_count);

      if (Str2Int(dividend_current) >= Str2Int(shifted_divisor)) {
          dividend_current = subtr(dividend_current, shifted_divisor);
          // Set the corresponding bit in the quotient to '1'
          quotient = quotient.update(k_loop_count as int, '1');
      }
      // else quotient bit is already '0'
      k_loop_count = k_loop_count + 1;
  }

  let mut final_quotient = trim_leading_zeros(quotient);
  if (final_quotient.len() == 0) {
    final_quotient = Seq::new(1, |i| '0');
  }

  let mut final_remainder = trim_leading_zeros(dividend_current);
  if (final_remainder.len() == 0) {
    final_remainder = Seq::new(1, |i| '0');
  }

  (seq_to_vec_char(final_quotient), seq_to_vec_char(final_remainder))
}
// </vc-code>

fn main() {}
}


