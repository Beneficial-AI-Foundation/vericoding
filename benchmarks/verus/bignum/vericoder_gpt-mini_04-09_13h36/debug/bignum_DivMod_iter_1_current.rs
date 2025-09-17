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
// <vc-helpers>
exec fn pow2(exp: nat) -> nat
{
    let mut i: nat = 0;
    let mut p: nat = 1;
    while i < exp
        invariant i <= exp
        invariant p == 2usize.pow(i)
        decreases exp - i
    {
        p = 2 * p;
        i = i + 1;
    }
    p
}

exec fn slice_to_nat(s: &[char]) -> nat
{
    let n = s.len();
    let mut i: usize = 0;
    let mut acc: nat = 0;
    while i < n
        invariant i <= n
        invariant acc == Str2Int(s@.subrange(0, i as int))
        decreases n - i
    {
        let c = s[i];
        let b: nat = if c == '1' { 1 } else { 0 };
        acc = 2 * acc + b;
        i = i + 1;
    }
    acc
}

proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
  requires 0 <= i && i < s.len() as int
  ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 })
{
    // By definition of Str2Int on a non-empty sequence (length i+1 > 0),
    // Str2Int of the sequence equals 2 * Str2Int(prefix) + last_bit.
    assert(forall |j: int| j == j); // trivial step to help verifier with unfolding
    assert(Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 }));
}

proof fn Str2Int_upper_bound(s: Seq<char>)
  ensures Str2Int(s) < pow2(s.len() as nat)
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(0 < pow2(0));
    } else {
        let m = s.len() as int - 1;
        let pref = s.subrange(0, m as int + 0); // prefix of length m
        Str2Int_upper_bound(pref);
        // s.len() = m+1
        // Str2Int(s) = 2 * Str2Int(pref) + bit, and by IH Str2Int(pref) < 2^m
        // So Str2Int(s) <= 2*(2^m - 1) + 1 = 2^(m+1) - 1 < 2^(m+1)
        assert(Str2Int(s) < pow2(s.len() as nat));
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    // convert divisor to nat
    let D: nat = slice_to_nat(divisor);
    // dividend length
    let n: usize = dividend.len();

    // quotient vector and remainder nat
    let mut qvec: Vec<char> = Vec::new();
    let mut rem: nat = 0;

    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant qvec.len() == i
        invariant rem < D
        invariant Str2Int(dividend@.subrange(0, i as int)) == D * Str2Int(qvec@.subrange(0, i as int)) + rem
        decreases n - i
    {
        let c = dividend[i];
        let b: nat = if c == '1' { 1 } else { 0 };

        // Str2Int relation for extended prefix of dividend
        assert(Str2Int(dividend@.subrange(0, i as int + 1)) == 2 * Str2Int(dividend@.subrange(0, i as int)) + (if c == '1' {1} else {0}));

        let rem2 = 2 * rem + b;
        if rem2 >= D {
            rem = rem2 - D;
            qvec.push('1');
// </vc-code>

fn main() {}
}