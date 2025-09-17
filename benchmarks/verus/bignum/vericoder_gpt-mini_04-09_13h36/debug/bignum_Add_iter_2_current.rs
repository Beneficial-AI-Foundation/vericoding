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
  ensures BitsValLSB(s + seq_one(b)) ==
          BitsValLSB(s) + (if b == '1' { Pow2(s.len() as nat) } else { 0 })
  decreases s.len()
{
    if s.len() == 0 {
        // s = []
        assert(BitsValLSB(seq_one(b)) == (if b == '1' { 1 } else { 0 }));
        assert(BitsValLSB(Seq::<char>::empty()) == 0);
        assert(Pow2(0) == 1);
    } else {
        // Use definition of BitsValLSB on concatenation:
        // (s + [b])[0] == s[0]
        assert((s + seq_one(b)).index(0) == s.index(0));
        // (s + [b]).subrange(1, s.len()+1) == s.subrange(1,s.len()) + [b]
        assert((s + seq_one(b)).subrange(1, s.len() + 1) ==
               s.subrange(1, s.len()) + seq_one(b));

        // Unfold BitsValLSB on s + [b]
        assert(BitsValLSB(s + seq_one(b)) ==
               (if s.index(0) == '1' { 1 } else { 0 }) +
               2 * BitsValLSB(s.subrange(1, s.len()) + seq_one(b)));

        // Apply induction hypothesis on the tail
        lemma_bitsvallsb_append(s.subrange(1, s.len()), b);

        // Now expand BitsValLSB(s)
        assert(BitsValLSB(s) ==
               (if s.index(0) == '1' { 1 } else { 0 }) +
               2 * BitsValLSB(s.subrange(1, s.len())));

        // Use lemma_pow2_double to relate Pow2(s.len()) and Pow2(s.len()-1)
        let sn1: nat = s.len() as nat - 1;
        lemma_pow2_double(sn1);

        // Now algebra to conclude:
        // BitsValLSB(s) + (if b=='1' {Pow2(s.len())} else {0})
        //   == (if s[0]=='1' {1} else {0}) + 2 * BitsValLSB(s.sub1) + (if b=='1' {2*Pow2(s.len()-1)} else {0})
        //   == (if s[0]=='1' {1} else {0}) + 2 * (BitsValLSB(s.sub1) + (if b=='1' {Pow2(s.len()-1)} else {0}))
        //   == BitsValLSB(s + [b])
        assert(BitsValLSB(s) + (if b == '1' { Pow2(s.len() as nat) } else { 0 }) ==
               (if s.index(0) == '1' { 1 } else { 0 }) +
               2 * (BitsValLSB(s.subrange(1, s.len())) +
                    (if b == '1' { Pow2(s.subrange(1, s.len()).len() as nat) } else { 0 })));

        // Combine with unfolded definition above to finish
    }
}

proof fn lemma_reverse_correspondence(s: Seq<char>, r: Seq<char>)
  requires s.len() == r.len()
  requires forall |i: int| 0 <= i && i < s.len() as int ==>
             r.index(i) == s.index(s.len() as int - 1 - i)
  ensures Str2Int(r) == BitsValLSB(s)
  decreases s.len()
{
    if s.len() == 0 {
        // both empty; Str2Int(empty)=0 and BitsValLSB(empty)=0
    } else {
        let first = s.index(0);
        let rest = s.subrange(1, s.len());
        let rlen = r.len();
        let r_last = r.index(rlen as int - 1);
        let r_rest = r.subrange(0, rlen - 1);

        // Show r_last == first
        assert(r_last == s.index(s.len() as int - 1 - (rlen as int - 1)));
        assert(s.len() as int - 1 - (rlen as int - 1) == 0);
        assert(r_last == first);

        // Show correspondence for r_rest and rest
        assert(forall |i: int|
            0 <= i && i < r_rest.len() as int ==>
                r_rest.index(i) == rest.index(rest.len() as int - 1 - i)
        );

        // Induction
        lemma_reverse_correspondence(rest, r_rest);

        // Unfold Str2Int on r
        assert(Str2Int(r) ==
               2 * Str2Int(r_rest) +
               (if r_last == '1' { 1 } else { 0 }));

        // By IH, Str2Int(r_rest) == BitsValLSB(rest)
        // So Str2Int(r) == 2*BitsValLSB(rest) + (if first=='1' {1} else {0})
        assert(Str2Int(r) ==
               2 * BitsValLSB(rest) +
               (if first == '1' { 1 } else { 0 }));

        // BitsValLSB(s) == (if first=='1'{1}else{0}) + 2*BitsValLSB(rest)
        assert(BitsValLSB(s) ==
               (if first == '1' { 1 } else { 0 }) + 2 * BitsValLSB(rest));

        // Conclude equality
        assert(Str2Int(r) == BitsValLSB(s));
    }
}

// Helper to build a one-element sequence from a char (spec-level)
spec fn seq_one(c: char) -> Seq<char> {
    Seq::from_slice(#[verus::internal] #[verus::spec] &[c])
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

        let p: nat = rev.len() as nat; // previous length
        let bit_is_one = x % 2 == 1;
        let ch = if bit_is_one { '1' } else { '0' };
        // push the new least-significant bit (as char) at the end (more significant in LSB-first)
        rev.push(ch);

        let old_x = x;
        x = x / 2;

        // Prove invariant after update
        proof {
            // old invariant: total == old_x * Pow2(p) + BitsValLSB(rev.subrange(0
// </vc-code>

fn main() {}
}