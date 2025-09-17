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
        let pref = s.subrange(0, m as int + 0);
        Str2Int_upper_bound(pref);
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
        let threshold: nat = pow2((len - i as nat) - 1);
        if x >= threshold {
            // bit = 1
            x = x - threshold;
            v.push('1');
            // show Str2Int(v@) updated correctly: new = 2*old + 1
            // Using Str2Int_subrange_last on constructed sequence: since we appended last char, the relation holds
            // We can assert the standard relation directly
            assert(Str2Int(v@.subrange(0, (i as int) + 1)) == 2 * Str2Int(v@.subrange(0, i as int)) + (if v@.index(i as int) == '1' { 1 } else { 0 }));
        } else {
            // bit = 0
            v.push('0');
            assert(Str2Int(v@.subrange(0, (i as int) + 1)) == 2 * Str2Int(v@.subrange(0, i as int)) + (if v@.index(i as int) == '1' { 1 } else { 0 }));
        }
        // update invariant: check Str2Int(v@) * 2^{len - (i+1)} + x == orig
        // From previous invariant: Str2Int(old_v) * 2^{len - i} + old_x == orig
        // And new Str2Int(v) == 2*Str2Int(old_v) + bit, and (len - (i+1)) = (len - i) - 1
        i = i + 1;
    }
    // at end i == L; from invariant x < 2^{0} => x == 0 and Str2Int(v@)*1 + 0 == orig => Str2Int(v@) == orig
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

    // If bi*(qi - q0i) has absolute value < bi, then qi - q0i == 0
    // Suppose qi - q0i != 0, then |bi*(qi - q0i)| >= bi, contradiction. So qi == q0i
    if qi != q0i {
        // then |bi*(qi - q0i)| >= bi, contradiction with previous bounds
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
        let c = dividend[i];
        let b: nat = if c == '1' { 1 } else { 0 };

        // Str2Int relation for extended prefix of dividend
        assert(Str2Int(dividend@.subrange(0, i as int + 1)) == 2 * Str2Int(dividend@.subrange(0, i as int)) + (if c == '1' {1} else {0}));

        let rem2 = 2 * rem + b;
        if rem2 >= D {
            rem = rem2 - D;
            qvec.push('1');
        } else {
            rem = rem2;
            qvec.push('0');
        }

        // After pushing, update invariant: Str2Int(qvec@.subrange(0, i+1)) == 2 * Str2Int(qvec@.subrange(0, i)) + bit
        assert(Str2Int(qvec@.subrange(0, i as int + 1)) == 2 * Str2Int(qvec@.subrange(0, i as int)) + (if qvec@.index(i as int) == '1' {1} else {0}));

        // Now prove the main invariant for i+1:
        // Str2Int(dividend[0..i+1]) == D * Str2Int(qvec[0..i+1]) + rem
        if rem2 >= D {
            // rem' = rem2 - D and bit = 1
            // LHS = 2 * Str2Int(dividend[0..i]) + b
            // By IH: Str2Int(dividend[0..i]) == D * Str2Int(qvec[0..i]) + rem
            // So LHS = 2*(D*Q + rem) + b = D*(2*Q + 1) + (2*rem + b - D)
            assert(2 * Str2Int(dividend@.subrange(0, i as int)) + b
                   == D * (2 * Str2Int(qvec@.subrange(0, i as int)) + 1) + (2 * rem + b - D));
            // rem updated to rem2 - D, and qvec appended '1', so invariant holds
        } else {
            // rem' = rem2 and bit = 0
            assert(2 * Str2Int(dividend@.subrange(0, i as int)) + b
                   == D * (2 * Str2Int(qvec@.subrange(0, i as int)) + 0) + (2 * rem + b));
        }

        i = i + 1;
    }

    // After loop: i == n
    // From invariant: Str2Int(dividend@) == D * Str2Int(qvec@) + rem and rem < D
    let total: nat = Str2Int(dividend@);
    assert(total == D * Str2Int(qvec@) + rem);
    assert(rem < D);

    // Use lemma to get quotient and remainder equalities
    div_mod_from_decomp(total, D, Str2Int(qvec@), rem);

    // Build remainder vector of length equal to divisor.len(), since rem < D <= 2^{divisor.len()}
    let remvec: Vec<char> = nat_to_bits_len(rem, divisor.len() as nat);

    // qvec is already a valid bitstring by invariant; remvec produced valid bitstring by nat_to_bits_len ensures
    (qvec, remvec)
}
// </vc-code>

fn main() {}
}