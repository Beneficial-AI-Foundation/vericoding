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
// Helper spec: sum of bits treating index 0 as least-significant (weight 2^0)
spec fn BitSum(b: Seq<char>) -> nat
  decreases b.len()
{
    if b.len() == 0 {
        0
    } else {
        2 * BitSum(b.subrange(1, b.len())) + (if b.index(0) == '1' { 1 } else { 0 })
    }
}

proof fn lemma_bits_rev_sum(b: Seq<char>)
  requires ValidBitString(b)
  ensures Str2Int(b.rev()) == BitSum(b)
  decreases b.len()
{
    if b.len() == 0 {
        // Str2Int(empty) == 0 and BitSum(empty) == 0
    } else {
        let n = b.len();
        let b0 = b.subrange(1, n);
        // Inductive hypothesis
        lemma_bits_rev_sum(b0);
        // By definition of Str2Int on b.rev():
        // Str2Int(b.rev()) == 2 * Str2Int((b.rev()).subrange(0, n-1)) + (if (b.rev()).index(n-1) == '1' then 1 else 0)
        // Note (b.rev()).subrange(0, n-1) == b0.rev() and (b.rev()).index(n-1) == b.index(0)
        assert(Str2Int(b.rev()) ==
               2 * Str2Int(b0.rev()) + (if b.index(0) == '1' { 1 } else { 0 }));
        // By definition of BitSum:
        assert(BitSum(b) == 2 * BitSum(b0) + (if b.index(0) == '1' { 1 } else { 0 }));
        // Use induction to replace Str2Int(b0.rev()) with BitSum(b0)
        assert(Str2Int(b0.rev()) == BitSum(b0));
        // Conclude
        assert(Str2Int(b.rev()) == BitSum(b));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let n1 = seq_to_nat(s1);
  let n2 = seq_to_nat(s2);
  let prod = n1 * n2;
  let res = nat_to_seq(prod);
  res
}
// </vc-code>

fn main() {}
}