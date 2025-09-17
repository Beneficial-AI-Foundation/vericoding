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
spec fn pow2(exp: nat) -> nat
  decreases exp
{
    if exp == 0 { 1 } else { 2 * pow2(exp - 1) }
}

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
{
    let L: usize = s.len();
    let mut i: usize = 0usize;
    let mut acc: nat = 0;
    while i < L
        invariant i <= L
        invariant acc == Str2Int(s@.subrange(0, i as int))
        decreases L - i
    {
        let idx: int = i as int;
        let c = s[i];
        let b: nat = if c == '1' { 1 } else { 0 };
        acc = 2 * acc + b;
        // relate updated acc with Str2Int for prefix length idx+1
        assert(Str2Int(s@.subrange(0, idx + 1)) == 2 * Str2Int(s@.subrange(0, idx)) + (if s@.index(idx) == '1' { 1 } else { 0 }));
        i = i + 1;
    }
    acc
}

proof fn Str2Int_subrange_last(s: Seq<char>, i: int)
  requires 0 <= i && i < s.len() as int
  ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 })
{
    // By definition of Str2Int
    assert(Str2Int(s.subrange(0, i + 1)) ==
           2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 }));
}

proof fn Str2Int_upper_bound(s: Seq<char>)
  ensures Str2Int(s) < pow2(s.len() as nat)
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(0 < pow2(0));
    } else {
        let m = s.len() as int - 1;
        let pref = s.subrange(0, m as int + 0);
        Str2Int_upper_bound(pref);
        // Now relate Str2Int(s) with Str2Int(pref)
        Str2Int_subrange_last(s, m);
        // From inductive hypothesis Str2Int(pref) < pow2(pref.len())
        // and Str2Int(s) = 2 * Str2Int(pref) + bit < 2 * pow2(pref.len()) <= pow2(s.len())
        assert(Str2Int(s) < pow2(s.len() as nat));
    }
}

exec fn nat_to_bits_len(mut x: nat, len: nat) -> Vec<char>
  requires x < pow2(len)
  ensures result.len() == len && Str2Int(result@) == old(x) && ValidBitString(result@)
{
    let orig: nat = x;
    let L: usize = len as usize;
    let mut i: usize = 0usize;
    let mut v: Vec<char> = Vec::new();
    // Invariant: Str2Int(v@) * 2^{len - i} + x == orig, x < 2^{len - i}, v.len() == i, ValidBitString(v@)
    while i < L
        invariant i <= L
        invariant v.len() == i
        invariant x < pow2(len - i as nat)
        invariant Str2Int(v@) * pow2(len - i as nat) + x == orig
        invariant ValidBitString(v@)
        decreases L - i
    {
        let idx: int = i as int;
        let threshold: nat = pow2((len - i as nat) - 1);
        if x >= threshold {
            // bit = 1
            x = x - threshold;
            v.push('1');
            assert(Str2Int(v@.subrange(0, idx + 1)) == 2 * Str2Int(v@.subrange(0, idx)) + (if v@.index(idx) == '1' { 1 } else { 0 }));
        } else {
            // bit = 0
            v.push('0');
            assert(Str2Int(v@.subrange(0, idx + 1)) == 2 * Str2Int(v@.subrange(0, idx)) + (if v@.index(idx) == '1' { 1 } else { 0 }));
        }
        i = i + 1;
    }
    v
}

proof fn div_mod_from_decomp(a: nat, b: nat, q: nat, r: nat)
  requires b > 0
  requires r < b
  requires a == b * q + r
  ensures q == a / b && r == a % b
{
    let q0: nat = a / b;
    let r0: nat = a % b;
    // standard properties:
    assert(a == b * q0 + r0);
    assert(r0 < b);

    // Work in int to reason about differences
    let bi: int = b as int;
    let qi: int = q as int;
    let q0i: int = q0 as int;
    let ri: int = r as int;
    let r0i: int = r0 as int;

    // b*(q - q0) == r0 - r
    assert(bi * (qi - q0i) == r0i - ri);

    // bound |r0 - r| < b
    assert(r0i >= 0);
    assert(ri >= 0);
    assert(r0i < bi);
    assert(ri < bi);
    // So -bi < r0i - ri < bi
    assert(!(r0i - ri >= bi));
    assert(!(r0i - ri <= -bi));

    // If qi != q0i then |bi*(qi - q0i)| >= bi, contradiction with previous bounds, hence qi == q0i
    if qi != q0i {
        if qi > q0i {
            assert(qi - q0i >= 1);
            // bi > 0 because b > 0
            assert(bi * (qi - q0i) >= bi);
        } else {
            assert(q0i - qi >= 1);
            assert(bi * (q0i - qi) >= bi);
            assert(bi * (qi - q0i) <= -bi);
        }
        // combine with bi*(qi - q0i) == r0i - ri leads to contradiction
        assert(false);
    }

    // hence qi == q0i
    assert(qi == q0i);
    assert(q == q0);
    // From a == b*q + r and a == b*q + r0, and q==q0, deduce r == r0
    assert(r == r0);
}
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
    assert(D == Str2Int(divisor@));

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
        invariant ValidBitString(qvec@)
        invariant Str2Int(dividend@.subrange(0, i as int)) == D * Str2Int(qvec@.subrange(0, i as int)) + rem
        decreases n - i
    {
        let idx: int = i as int;
        let c = dividend[i];
        let b: nat = if c == '1' { 1 } else { 0 };

        // Str2Int relation for extended prefix of dividend
        assert(Str2Int(dividend@.subrange(0, idx + 1)) == 2 * Str2Int(dividend@.subrange(0, idx)) + (if c == '1' {1} else {0}));

        let rem2 = 2 * rem + b;
        if rem2 >= D {
            rem = rem2 - D;
            qvec.push('1');
        } else {
            rem = rem2;
            qvec.push('0');
        }

        // After pushing, update invariant: Str2Int(qvec@.subrange(0, idx+1)) == 2 * Str2Int(qvec@.subrange(0, idx)) + bit
        assert(Str2Int(qvec@.subrange(0, idx + 1)) == 2 * Str2Int(qvec@.subrange(0, idx)) + (if qvec@.index(idx) == '1' {1} else {0}));

        // Now prove the main invariant for i+1:
        // Str2Int(dividend[0..i+1]) == D * Str2Int(qvec[0..i+1]) + rem
        if rem2 >= D {
            // rem' = rem2 - D and bit = 1
            assert(2 * Str2Int(dividend@.subrange(0, idx)) + b
                   == D * (2 * Str2Int(qvec@.subrange(0, idx)) + 1) + (2 * rem + b - D));
        } else {
            // rem' = rem2 and bit = 0
            assert(2 * Str2Int(dividend@.subrange(0, idx)) + b
                   == D * (2 * Str2Int(qvec@.subrange(0, idx)) + 0) + (2 * rem + b));
        }

        i = i + 1;
    }

    // After loop: i == n
    // From invariant: Str2Int(dividend@) == D * Str2Int(qvec@) + rem and rem < D
    let total: nat = Str2Int(dividend@);
    assert(total == D * Str2Int(qvec@) + rem);
    assert(rem < D);

    // Use lemma to get quotient and remainder equalities
    assert(D > 0);
    div_mod_from_decomp(total, D, Str2Int(qvec@), rem);

    // Build remainder vector of length equal to divisor.len(), since rem < D <= 2^{divisor.len()}
    // Prove rem < pow2(divisor.len())
    Str2Int_upper_bound(divisor@);
    assert(D < pow2(divisor.len() as nat));
    assert(rem < pow2(divisor.len() as nat));

    let remvec: Vec<char> = nat_to_bits_len(rem, divisor.len() as nat);

    // qvec is already a valid bitstring by invariant; remvec produced valid bitstring by nat_to_bits_len ensures
    (qvec, remvec)
}
// </vc-code>

fn main() {}
}