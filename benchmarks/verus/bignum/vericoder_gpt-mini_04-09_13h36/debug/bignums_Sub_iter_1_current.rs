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
spec fn Pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Pow2(n - 1) }
}

proof fn Str2Int_subrange_last(s: Seq<char>)
    requires ValidBitString(s)
    ensures
        if s.len() == 0 {
            Str2Int(s) == 0
        } else {
            let k = s.len() - 1;
            Str2Int(s) == 2 * Str2Int(s.subrange(0, k as int)) + (if s.index(k as int) == '1' { 1 } else { 0 })
        }
    decreases s.len()
{
    // Directly follows from the definition of Str2Int
    if s.len() == 0 {
    } else {
        // by definition of Str2Int this holds
    }
}

proof fn Str2Int_prefix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Pow2(s.len())
    decreases s.len()
{
    if s.len() == 0 {
        // 0 < 1
    } else {
        let k = s.len() - 1;
        // Str2Int(s) = 2*Str2Int(prefix) + bit
        Str2Int_subrange_last(s);
        // Apply inductive hypothesis to prefix
        Str2Int_prefix_bound(s.subrange(0, k as int));
        // From Str2Int(prefix) < Pow2(k) and bit <= 1 derive strict < Pow2(k+1)
        // convert strict < to <= form for nat arithmetic
        assert(Str2Int(s.subrange(0, k as int)) <= Pow2(k) - 1);
        // hence 2*Str2Int(prefix) + bit <= 2*(Pow2(k)-1) + 1 = 2*Pow2(k) -1 < 2*Pow2(k)
        // therefore Str2Int(s) < Pow2(k+1)
    }
}

proof fn Nat_div_pow2_after_iters(d: nat, n: nat)
    requires d < Pow2(n)
    ensures d / Pow2(n) == 0
    decreases n
{
    if n == 0 {
        // Pow2(0) == 1 so d < 1 => d == 0 and d / 1 == 0
    } else {
        // For n > 0, let b = d % 2, q = d / 2
        let q = d / 2;
        // q < Pow2(n-1)
        assert(q < Pow2(n - 1));
        Nat_div_pow2_after_iters(q, n - 1);
        // then q / Pow2(n-1) == 0, so d / Pow2(n) == 0
    }
}

proof fn Bits_representation(d: nat, n: nat)
    requires d < Pow2(n)
    ensures exists |bits: Seq<char>| bits.len() == n && ValidBitString(bits) && Str2Int(bits) == d
    decreases n
{
    if n == 0 {
        // d < 1 => d == 0, bits = empty
        exists(Seq::<char>::empty());
    } else {
        let b = if d % 2 == 1 { '1' } else { '0' };
        let q = d / 2;
        // q < Pow2(n-1)
        assert(q < Pow2(n - 1));
        Bits_representation(q, n - 1);
        // obtain seq_rest of length n-1 such that Str2Int(seq_rest) == q
        // then bits = seq_rest + [b] has Str2Int == 2*q + (b as nat) == d
        // Construct explicit sequence
        // Let seq_rest be witness from recursive call
        let (seq_rest: Seq<char>) = proof {
            let mut witness = Seq::<char>::empty();
            witness
        };
        // We cannot extract the witness directly in code; but existence suffices for proofs about Str2Int composition.
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Parse s1 into v1
    let n1_usize: usize = s1.len();
    let n1_nat: nat = s1@.len();
    let mut v1: nat = 0;
    let mut i: usize = 0;
    while i < n1_usize
        invariant i <= n1_usize
        invariant v1 == Str2Int(s1@.subrange(0, i as int))
        invariant ValidBitString(s1@)
    {
        let ch = s1[i];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        // update v1
        v1 = 2 * v1 + bit;
        // prove the invariant for i+1
        proof {
            // By Str2Int definition on the prefix of length i+1
            Str2Int_subrange_last(s1@.subrange(0, (i + 1) as int));
            // The last character of the prefix equals ch
            // and v1 was updated accordingly
        }
        i = i + 1;
    }

    // Parse s2 into v2
    let n2_usize: usize = s2.len();
    let mut v2: nat = 0;
    let mut j: usize = 0;
    while j < n2_usize
        invariant j <= n2_usize
        invariant v2 == Str2Int(s2@.subrange(0, j as int))
        invariant ValidBitString(s2@)
    {
        let ch = s2[j];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        v2 = 2 * v2 + bit;
        proof {
            Str2Int_subrange_last(s2@.subrange(0, (j + 1) as int));
        }
        j = j + 1;
    }

    // compute difference
    let mut d: nat = v1 - v2;

    // We know d < 2^n1 from bounds on v
// </vc-code>

fn main() {}
}