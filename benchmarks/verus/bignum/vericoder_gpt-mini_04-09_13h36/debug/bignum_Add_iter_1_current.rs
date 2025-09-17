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
// <vc-helpers>
spec fn Pow2(n: nat) -> nat
  decreases n
{
    if n == 0 { 1 } else { 2 * Pow2(n - 1) }
}

spec fn BitsValLSB(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.index(0) == '1' { 1nat } else { 0nat })
          + 2 * BitsValLSB(s.subrange(1, s.len()))
    }
}

proof fn lemma_pow2_double(n: nat)
  ensures Pow2(n + 1) == 2 * Pow2(n)
  decreases n
{
    if n == 0 {
        assert(Pow2(1) == 2 * Pow2(0));
    } else {
        lemma_pow2_double(n - 1);
        assert(Pow2(n + 1) == 2 * Pow2(n));
    }
}

proof fn lemma_bitsvallsb_append(s: Seq<char>, b: char)
  ensures BitsValLSB(s + Seq::<char>::from_seq(Seq::from_slice(#[verus::internal] #[verus::spec] &[b]))) ==
          BitsValLSB(s) + (if b == '1' { Pow2(s.len() as nat) } else { 0 })
  decreases s.len()
{
    // We will not actually use this specific form of append in proofs;
    // instead, proofs in Add will use unfolding of BitsValLSB and Pow2 facts directly.
}

proof fn lemma_reverse_correspondence(s: Seq<char>, r: Seq<char>)
  requires s.len() == r.len()
  requires forall |i: int| 0 <= i && i < s.len() as int ==>
             r.index(i) == s.index(s.len() as int - 1 - i)
  ensures Str2Int(r) == BitsValLSB(s)
  decreases s.len()
{
    if s.len() == 0 {
        // both are empty
    } else {
        let first = s.index(0);
        let rest = s.subrange(1, s.len());
        let rlen = r.len();
        // r_last is last element of r
        let r_last = r.index(rlen as int - 1);
        // r_rest is r without its last element
        let r_rest = r.subrange(0, rlen - 1);
        // Show r_last == first
        assert(r_last == s.index(s.len() as int - 1 - (rlen as int - 1)));
        // s.len() - 1 - (rlen - 1) = 0
        assert(s.len() as int - 1 - (rlen as int - 1) == 0);
        assert(r_last == first);

        // Show for all i in r_rest, r_rest[i] == rest[rest.len()-1 - i]
        assert(forall |i: int|
            0 <= i && i < r_rest.len() as int ==>
                r_rest.index(i) == rest.index(rest.len() as int - 1 - i)
        );
        // Now apply induction
        lemma_reverse_correspondence(rest, r_rest);

        // Now Str2Int(r) = 2 * Str2Int(r_rest) + bit_last
        // by unfolding Str2Int on r: last char is LSB
        // Using Str2Int definition:
        // Str2Int(r) = 2 * Str2Int(r_rest) + (if r_last == '1' {1} else {0})
        // By inductive hypothesis Str2Int(r_rest) == BitsValLSB(rest)
        // So Str2Int(r) == 2 * BitsValLSB(rest) + (if first == '1' {1} else {0})
        // Which equals BitsValLSB(s)
    }
}

// Helper to build a one-element sequence from a char (spec-level)
spec fn seq_one(c: char) -> Seq<char> {
    Seq::from_slice(#[verus::internal] #[verus::spec] &[c])
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let total: nat = Str2Int(s1@) + Str2Int(s2@);

    // rev will hold bits in LSB-first order (index 0 is LSB)
    let mut rev: Vec<char> = Vec::new();

    // x is the remaining high part of total not yet represented by rev
    let mut x: nat = total;

    // Loop: extract least-significant bits of x and push them into rev (LSB-first)
    while x > 0 {
        invariant total == x * Pow2(rev.len() as nat) + BitsValLSB(rev@);
        invariant ValidBitString(rev@);
        decreases x;

        let bit_is_one = x % 2 == 1;
        let ch = if bit_is_one { '1' } else { '0' };
        rev.push(ch);

        // update x
        let old_x = x;
        x = x / 2;

        // Now prove the invariant holds after the update
        // Let p = previous rev.len() (before push)
        // previous invariant: total == old_x * Pow2(p) + BitsValLSB(old_rev)
        // After push, new_rev has length p+1 and BitsValLSB(new_rev) = BitsValLSB(old_rev) + (if bit_is_one then Pow2(p) else 0)
        // And old_x == 2 * x + (if bit_is_one then 1 else 0)
        proof {
            let p = rev.len() as nat - 1; // previous p
            // Use lemma_pow2_double to relate Pow2(p+1) and Pow2(p)
            lemma_pow2_double(p);
            // Unfold BitsValLSB for new_rev:
            // BitsValLSB(rev@) == (if rev@[0]=='1' then 1 else 0) + 2 * BitsValLSB(rev@.subrange(1,...))
            // But rather than unfolding generally, we reason via arithmetic:
            // From previous invariant:
            assert(total == old_x * Pow2(p) + BitsValLSB(rev.subrange(0, rev.len() - 1)@));
            // Compute contribution of appended bit:
            if bit_is_one {
                assert(BitsValLSB(rev@) == BitsValLSB(rev.subrange(0, rev.len() - 1)@) + Pow2(p));
            } else {
                assert(BitsValLSB(rev@) == Bits
// </vc-code>

fn main() {}
}