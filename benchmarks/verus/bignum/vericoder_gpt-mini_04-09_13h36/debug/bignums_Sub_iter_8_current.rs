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

spec fn BitsValue_LSB_first(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k = s.len() - 1;
        BitsValue_LSB_first(s.subrange(0, k as int))
            + (if s.index(k as int) == '1' { Pow2(k as nat) } else { 0 })
    }
}

proof fn BitsValue_append_last(s: Seq<char>, last: char)
    requires ValidBitString(s)
    requires last == '0' || last == '1'
    ensures BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 })
    decreases s.len()
{
    if s.len() == 0 {
        // s == []
        // By definition:
        assert(BitsValue_LSB_first(s) == 0);
        assert(BitsValue_LSB_first(s + seq![last]) == (if last == '1' { Pow2(0) } else { 0 }));
        assert(Pow2(0) == Pow2(s.len() as nat));
        // Combine
        assert(BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 }));
    } else {
        // For non-empty s, by definition of BitsValue_LSB_first on (s + [last]),
        // the last element of (s + [last]) is `last` and the prefix is `s`.
        // Hence the definition yields the required equality directly.
        assert(BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 }));
    }
}

// Relate BitsValue_LSB_first(s) with Str2Int(Seq_rev(s))
proof fn BitsValue_LSB_first_eq_Str2Int_rev(s: Seq<char>)
    requires ValidBitString(s)
    ensures BitsValue_LSB_first(s) == Str2Int(Seq_rev(s))
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let k = s.len() - 1;
        let t = s.subrange(0, k as int);
        let last
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
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

spec fn BitsValue_LSB_first(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k = s.len() - 1;
        BitsValue_LSB_first(s.subrange(0, k as int))
            + (if s.index(k as int) == '1' { Pow2(k as nat) } else { 0 })
    }
}

proof fn BitsValue_append_last(s: Seq<char>, last: char)
    requires ValidBitString(s)
    requires last == '0' || last == '1'
    ensures BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 })
    decreases s.len()
{
    if s.len() == 0 {
        // s == []
        // By definition:
        assert(BitsValue_LSB_first(s) == 0);
        assert(BitsValue_LSB_first(s + seq![last]) == (if last == '1' { Pow2(0) } else { 0 }));
        assert(Pow2(0) == Pow2(s.len() as nat));
        // Combine
        assert(BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 }));
    } else {
        // For non-empty s, by definition of BitsValue_LSB_first on (s + [last]),
        // the last element of (s + [last]) is `last` and the prefix is `s`.
        // Hence the definition yields the required equality directly.
        assert(BitsValue_LSB_first(s + seq![last]) == BitsValue_LSB_first(s) + (if last == '1' { Pow2(s.len() as nat) } else { 0 }));
    }
}

// Relate BitsValue_LSB_first(s) with Str2Int(Seq_rev(s))
proof fn BitsValue_LSB_first_eq_Str2Int_rev(s: Seq<char>)
    requires ValidBitString(s)
    ensures BitsValue_LSB_first(s) == Str2Int(Seq_rev(s))
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let k = s.len() - 1;
        let t = s.subrange(0, k as int);
        let last
// </vc-code>

fn main() {}
}