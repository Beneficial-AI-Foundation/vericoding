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
    // Direct from definition; nothing to do
    if s.len() == 0 {
    } else {
    }
}

proof fn Str2Int_prefix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) <= Pow2(s.len()) - 1
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let k = s.len() - 1;
        Str2Int_subrange_last(s);
        Str2Int_prefix_bound(s.subrange(0, k as int));
    }
}

// Value of a sequence of bits interpreted LSB-first:
// i.e., s[0] has weight 2^0, s[1] has weight 2^1, ..., s[len-1] has weight 2^{len-1}
spec fn BitsValue_LSB_first(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k = s.len() - 1;
        BitsValue_LSB_first(s.subrange(0, k as int))
            + (if s.index(k as int) == '1' { Pow2(k) } else { 0 })
    }
}

// Reverse a sequence
spec fn Seq_rev(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let k = s.len() - 1;
        seq![ s.index(k as int) ] + Seq_rev(s.subrange(0, k as int))
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
        // a + b == b
    } else {
        let k = a.len() - 1;
        // a = prefix ++ [last]
        // Use definition on a + b:
        // Str2Int(a + b) = 2 * Str2Int((a + b).subrange(0, (a + b).len()-1)) + lastbit
        // where lastbit is (a+b).index((a+b).len()-1) which is b's last bit if b non-empty, else a's last bit.
        // We can proceed by induction peeling off last of a.
        Str2Int_concat(a.subrange(0, k as int), b);
    }
}

// Relate BitsValue_LSB_first(s) with Str2Int(Seq_rev(s))
proof fn BitsValue_LSB_first_eq_Str2Int_rev(s: Seq<char>)
    requires ValidBitString(s)
    ensures BitsValue_LSB_first(s) == Str2Int(Seq_rev(s))
    decreases s.len()
{
    if s.len() == 0 {
        // both zero
    } else {
        let k = s.len() - 1;
        // s = t ++ [last], where t = s.subrange(0,k)
        let t = s.subrange(0, k as int);
        let last = s.index(k as int);
        BitsValue_LSB_first_eq_Str2Int_rev(t);
        // Seq_rev(s) = seq![last] + Seq_rev(t)
        // Then Str2Int(Seq_rev(s)) = Pow2(Seq_rev(t).len())*Str2Int(seq![last]) + Str2Int(Seq_rev(t))
        // Seq_rev(t).len() == t.len() == k
        // Str2Int(seq![last]) == (if last=='1' {1} else {0})
        // So we get equality with BitsValue_LSB_first(s)
        Str2Int_concat(seq![last], Seq_rev(t));
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
    // Implementation of Sub: compute numeric values then convert difference to bits.

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

    while d > 0
        invariant accum_rev <= orig
        invariant orig == accum_rev + d * Pow2(r_rev.len())
        invariant r
// </vc-code>

fn main() {}
}