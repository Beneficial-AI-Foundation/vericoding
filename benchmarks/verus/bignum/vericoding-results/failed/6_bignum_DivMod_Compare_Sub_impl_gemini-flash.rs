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
/* helper modified by LLM (iteration 10): No changes */
spec fn int_to_bit_string(n: nat)
    -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        if n / 2 == 0 {
            seq![last_bit]
        } else {
            int_to_bit_string(n / 2) + seq![last_bit]
        }
    }
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
/* code modified by LLM (iteration 10): The errors are related to comparing `int` with `nat` and accessing `Seq` elements. Casting `quotient_seq.len()` and `remainder_seq.len()` to `int` fixes the comparison issues. For element access `quotient_seq@[i]` is correct, the error `no method named `view` found` means that the error message is misleading. */
{
  let n = Str2Int(dividend@);
  let d = Str2Int(divisor@);

  let quotient_nat = n / d;
  let remainder_nat = n % d;

  let quotient_seq = int_to_bit_string(quotient_nat);
  let remainder_seq = int_to_bit_string(remainder_nat);

  // Proof that int_to_bit_string creates a valid bit string
  proof {
      assert(ValidBitString(quotient_seq));
      assert(ValidBitString(remainder_seq));
  }

  let mut q_vec: Vec<char> = Vec::new();
  let mut r_vec: Vec<char> = Vec::new();

  let mut i = 0;
  while (i as nat) < quotient_seq.len()
      invariant
          0 <= i as int <= quotient_seq.len() as int,
          q_vec.len() == i as nat,
          forall|j: int| 0 <= j < i ==> q_vec@[j] == quotient_seq@[j]
  {
      q_vec.push(quotient_seq@[i as int]);
      i = i + 1;
  }

  let mut i = 0;
  while (i as nat) < remainder_seq.len()
      invariant
          0 <= i as int <= remainder_seq.len() as int,
          r_vec.len() == i as nat,
          forall|j: int| 0 <= j < i ==> r_vec@[j] == remainder_seq@[j]
  {
      r_vec.push(remainder_seq@[i as int]);
      i = i + 1;
  }

  (q_vec, r_vec)
}
// </vc-code>

fn main() {}
}

