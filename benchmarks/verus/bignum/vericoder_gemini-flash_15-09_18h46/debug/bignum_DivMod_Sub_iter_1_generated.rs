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
spec fn LeStr(s1: Seq<char>, s2: Seq<char>) -> bool {
    Str2Int(s1) <= Str2Int(s2)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let s_dividend = Seq::new(dividend.len(), |i| dividend[i]);
  let s_divisor = Seq::new(divisor.len(), |i| divisor[i]);

  let mut quotient = Vec::<char>::new();
  let mut remainder = Vec::<char>::new();
  let mut i: int = 0;

  f!(
    assert i <= s_dividend.len() as int;
  );

  while i < s_dividend.len() as int
    invariant
      0 <= i && i <= s_dividend.len() as int,
      ValidBitString(s_dividend),
      ValidBitString(s_divisor),
      ValidBitString(quotient@),
      ValidBitString(remainder@),
      Str2Int(s_divisor) > 0,
      // This invariant needs to relate the current state to the final result of division.
      // It's the most complex part of a division algorithm proof.
      // A common invariant for schoolbook division is:
      // Str2Int(s_dividend.subrange(0, i)) == Str2Int(quotient@) * Str2Int(s_divisor) + Str2Int(remainder@) * 2^(s_dividend.len() as int - remainder.len() as int)
      // This is complicated by the fact that `remainder` is built up.
      // Let's reformulate it based on the typical 'append current digit to current remainder' approach:
      Str2Int(s_dividend.subrange(0, i)) == Str2Int(quotient@) * Str2Int(s_divisor) + Str2Int(remainder@),

      // Additional invariant for remainder size to ensure single digit appending logic works
      remainder.len() <= s_divisor.len(),


    decreases (s_dividend.len() - i)
  {
    f!
    (
      assert i < s_dividend.len() as int;
      assert (s_dividend.subrange(0, i)).len() == i;
      assert_by_equality { Str2Int(s_dividend.subrange(i, i + 1)) == if s_dividend[i] == '1' { 1 } else { 0 } };
    );

    remainder.push(s_dividend[i]);

    f!(
      assert ValidBitString(remainder@);
      assert remainder@.len() == (remainder.len());
      assert LeStr(s_divisor, remainder@) == (Str2Int(s_divisor) <= Str2Int(remainder@)); // This needs proof
    );

    if LeStr(s_divisor, remainder@) {
      // Perform subtraction like 'remainder - divisor'
      // This requires a helper or complex in-line logic.
      // For now, let's assume `SubStr` exists and works as expected.
      let sub_res = SubStr(remainder@, s_divisor);
      proof {
        // Need to prove that SubStr result maintains ValidBitString
        // if both inputs are valid.
        ensures(ValidBitString(sub_res))
      }
      remainder = Vec::from_seq(sub_res);
      quotient.push('1');
    } else {
      quotient.push('0');
    }
    i = i + 1;
    f!(
      assert i <= s_dividend.len() as int;
    );
  }

  // After the loop, the final remainder for the actual result might need trimming leading zeros if allowed.
  // And the quotient might need leading zero trimming.
  // This current `remainder` is the final remainder.
  // The loop invariant ensures Str2Int(s_dividend) == Str2Int(quotient@) * Str2Int(s_divisor) + Str2Int(remainder@)

  // Trim leading zeros from quotient if it's not "0" itself.
  let trimmed_quotient = trim_leading_zeros(quotient@);

  // ensure postconditions
  // ensures ValidBitString(trimmed_quotient) && ValidBitString(remainder@)
  // ensures Str2Int(trimmed_quotient) == Str2Int(s_dividend) / Str2Int(s_divisor)
  // ensures Str2Int(remainder@) == Str2Int(s_dividend) % Str2Int(s_divisor)

  (Vec::from_seq(trimmed_quotient), remainder)
}
// </vc-code>

fn main() {}
}

