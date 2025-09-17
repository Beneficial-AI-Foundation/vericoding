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

proof fn Pow2_succ(n: nat)
    ensures Pow2(n + 1) == 2 * Pow2(n)
{
    if n == 0 {
    } else {
        Pow2_succ(n - 1);
    }
}

proof fn BitsValue_append_last(s: Seq<char>, last: char)
    requires ValidBitString(s)
    requires last == '0' || last == '1'
    ensures BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len()) } else { 0 })
    decreases s.len()
{
    if s.len() == 0 {
        // s + [last] is sequence of length 1; follows from definition
    } else {
        let k = s.len() - 1;
        BitsValue_append_last(s.subrange(0, k as int), s.index(k as int));
    }
}

// Relate BitsValue_LSB_first(s) with Str2Int(Seq_rev(s))
// (Provided earlier; duplication to ensure availability)
proof fn BitsValue_LSB_first_eq_Str2Int_rev(s: Seq<char>)
    requires ValidBitString(s)
    ensures BitsValue_LSB_first(s) == Str2Int(Seq_rev(s))
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let k = s.len() - 1;
        let t = s.subrange(0, k as int);
        let last = s.index(k as int);
        BitsValue_LSB_first_eq_Str2Int_rev(t);
        Str2Int_concat(seq![last], Seq_rev(t));
    }
}

// Str2Int concatenation lemma: Str2Int(a + b) = Pow2(b.len()) * Str2Int(a) + Str2Int(b)
proof fn Str2Int_concat(a: Seq<char>, b: Seq<char>)
    requires ValidBitString(a)
    requires ValidBitString(b)
    ensures Str2Int(a + b) == Pow2(b.len()) * Str2Int(a) + Str2Int(b)
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        let k = a.len() - 1;
        Str2Int_concat(a.subrange(0, k as int), b);
    }
}

// Str2Int on singleton sequence
proof fn Str2Int_singleton(c: char)
    requires c == '0' || c == '1'
    ensures Str2Int(seq![c]) == (if c == '1' { 1 } else { 0 })
{
    // follows from definition
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = s1.len();
    let n2 = s2.len();

    // Compute x1 = Str2Int(s1@)
    let mut i: usize = 0;
    let mut x1: nat = 0;
    while i < n1
        invariant i <= n1
        invariant x1 == Str2Int(s1@.subrange(0, i as int))
        decreases n1 - i
    {
        let c = s1[i];
        assert(c == '0' || c == '1');
        let bit: nat = if c == '1' { 1 } else { 0 };
        x1 = 2 * x1 + bit;
        i += 1;
    }
    assert(x1 == Str2Int(s1@));

    // Compute x2 = Str2Int(s2@)
    let mut j: usize = 0;
    let mut x2: nat = 0;
    while j < n2
        invariant j <= n2
        invariant x2 == Str2Int(s2@.subrange(0, j as int))
        decreases n2 - j
    {
        let c = s2[j];
        assert(c == '0' || c == '1');
        let bit: nat = if c == '1' { 1 } else { 0 };
        x2 = 2 * x2 + bit;
        j += 1;
    }
    assert(x2 == Str2Int(s2@));

    // difference (non-negative by precondition)
    let diff: nat = x1 - x2;

    // Build LSB-first representation into r_rev, while maintaining numeric invariant
    let mut d: nat = diff;
    let orig: nat = diff;
    let mut r_rev: Vec<char> = Vec::new();
    let mut accum_rev: nat = 0; // numeric value of r_rev interpreted LSB-first

    // Invariants:
    // - accum_rev equals BitsValue_LSB_first(r_rev@)
    // - orig == accum_rev + d * Pow2(r_rev.len())
    // - r_rev contains only '0' or '1'
    while d > 0
        invariant accum_rev == BitsValue_LSB_first(r_rev@)
        invariant orig == accum_rev + d * Pow2(r_rev.len())
        invariant forall |k: int| 0 <= k && k < r_rev.len() as int ==> (r_rev@[k] == '0' || r_rev@[k] == '1')
        decreases d
    {
        let b: nat = d % 2;
        let bit_char: char = if b == 1 { '1' } else { '0' };

        let old_len = r_rev.len();
        let old_seq = r_rev@;

        // Update accum_rev to include the new bit at weight Pow2(old_len)
        let new_accum = accum_rev + b * Pow2(old_len);

        // Push the new (LSB) bit
        r_rev.push(bit_char);
        accum_rev = new_accum;

        // Prove accum_rev equals BitsValue_LSB_first(r_rev@)
        // r_rev@ == old_seq + seq![bit_char]
        assert(r_rev@ == old_seq + seq![bit_char]);
        // By definition of BitsValue_LSB_first on append:
        BitsValue_append_last(old_seq, bit_char);
        assert(BitsValue_LSB_first(r_rev@) == BitsValue_LSB_first(old_seq) + (if bit_char == '1' { Pow2(old_len) } else { 0 }));
        // By the invariant accum_rev == BitsValue_LSB_first(old_seq) before update,
        // and by construction of new_accum, accum_rev == BitsValue_LSB_first(r_rev@).
        // (We updated accum_rev to new_accum above.)

        // Update d: divide by 2
        d = d / 2;

        // Prove orig == accum_rev + d * Pow2(r_rev.len())
        // Before update: orig == old_accum + (b + 2 * d) * Pow2(old_len)
        // After update: accum_rev == old_accum + b * Pow2(old_len), r_rev.len() == old_len + 1
        // So RHS becomes accum_rev + d * Pow2(old_len + 1) == accum_rev + d * Pow2(r_rev.len())
        Pow2_succ(old_len); // Pow2(old_len+1) == 2*Pow2(old_len)
    }

    // Now d == 0, so accum_rev == orig
    assert(d == 0);
    assert(accum_rev == orig);

    // Build result by reversing r_rev (r_rev is LSB-first; res must be MSB-first)
    let rr = r_rev@; // snapshot of sequence to reason about
    let mut res: Vec<char> = Vec::new();
    let m = r_rev.len();
    let mut idx: usize = 0;
    while idx < m
        invariant idx <= m
        // res@ is prefix of Seq_rev(rr) of length idx
        invariant res@ == Seq_rev(rr).subrange(0, idx as int)
        decreases m - idx
    {
        // push rr[m - 1 - idx]
        let ch = rr[(m - 1 - idx) as int];
        assert(ch == '0' || ch == '1');
        res.push(ch);
        idx += 1;
    }
    // At the end res@ == Seq_rev(rr)
    assert(res@ == Seq_rev(rr));

    // ValidBitString(res@) holds because we only pushed '0'/'1'
    assert(forall |k: int| 0 <= k && k < res@.len() as int ==> (res@.index(k) == '0' || res@.index(k) == '1'));

    // Relate Str2Int(res@) to orig:
    // BitsValue_LSB_first(rr) == Str2Int(Seq_rev(rr)) by lemma
    BitsValue_LSB_first_eq_Str2Int_rev(rr);
    // accum_rev == BitsValue_LSB_first(rr)
    assert(accum_rev == BitsValue_LSB_first(rr));
    // accum_rev == orig
    assert(orig == accum_rev);
    // res@ == Seq_rev(rr) so Str2Int(res@) == Str2Int(Seq_rev(rr))
    assert(Str2Int(res@) == BitsValue_LSB_first(rr));

    (res)
}
// </vc-code>

fn main() {}
}