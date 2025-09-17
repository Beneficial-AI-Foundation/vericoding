use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): ensure loop measures/invariants are valid, maintain ValidBitString throughout, and avoid fragile in-place reverse by using a second vector */
    let mut v1: u128 = 0;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
        decreases (s1.len() - i) as int
    {
        let bit1 = if s1[i] == '1' { 1u128 } else { 0u128 };
        v1 = v1.wrapping_mul(2).wrapping_add(bit1);
        i += 1;
    }
    let mut v2: u128 = 0;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            j <= s2.len(),
        decreases (s2.len() - j) as int
    {
        let bit2 = if s2[j] == '1' { 1u128 } else { 0u128 };
        v2 = v2.wrapping_mul(2).wrapping_add(bit2);
        j += 1;
    }
    let mut sum: u128 = v1.wrapping_add(v2);

    if sum == 0 {
        let mut z: Vec<char> = Vec::new();
        z.push('0');
        proof { assert(ValidBitString(z@)); }
        return z;
    }

    let mut tmp: Vec<char> = Vec::new();
    let mut k: usize = 0;
    while (sum > 0) && (k < 128)
        invariant
            k <= 128,
            ValidBitString(tmp@),
        decreases (128 - k) as int
    {
        let b = sum & 1u128;
        tmp.push(if b == 1u128 { '1' } else { '0' });
        sum >>= 1;
        k += 1;
    }

    let n = tmp.len();
    let mut res: Vec<char> = Vec::new();
    let mut t: usize = 0;
    while t < n
        invariant
            t <= n,
            ValidBitString(res@),
        decreases (n - t) as int
    {
        let idx = n - 1 - t;
        let c = tmp[idx];
        // c is either '0' or '1' since tmp only contains those
        res.push(c);
        t += 1;
    }

    proof { assert(ValidBitString(res@)); }
    res
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix loop measures/invariants, maintain ValidBitString, avoid in-place reverse, and guard against div-by-zero at runtime */
    let mut a: u128 = 0;
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
        decreases (dividend.len() - i) as int
    {
        let bit = if dividend[i] == '1' { 1u128 } else { 0u128 };
        a = a.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let mut b: u128 = 0;
    let mut j: usize = 0;
    while j < divisor.len()
        invariant
            j <= divisor.len(),
        decreases (divisor.len() - j) as int
    {
        let bit = if divisor[j] == '1' { 1u128 } else { 0u128 };
        b = b.wrapping_mul(2).wrapping_add(bit);
        j += 1;
    }

    let q_val: u128 = if b == 0 { 0 } else { a / b };
    let r_val: u128 = if b == 0 { a } else { a % b };

    // Build quotient vector
    let mut q_out: Vec<char> = Vec::new();
    if q_val == 0 {
        q_out.push('0');
    } else {
        let mut tmp: Vec<char> = Vec::new();
        let mut q = q_val;
        let mut k: usize = 0;
        while (q > 0) && (k < 128)
            invariant
                k <= 128,
                ValidBitString(tmp@),
            decreases (128 - k) as int
        {
            let bq = q & 1u128;
            tmp.push(if bq == 1u128 { '1' } else { '0' });
            q >>= 1;
            k += 1;
        }
        let n = tmp.len();
        let mut t: usize = 0;
        while t < n
            invariant
                t <= n,
                ValidBitString(q_out@),
            decreases (n - t) as int
        {
            let idx = n - 1 - t;
            let c = tmp[idx];
            q_out.push(c);
            t += 1;
        }
    }

    // Build remainder vector
    let mut r_out: Vec<char> = Vec::new();
    if r_val == 0 {
        r_out.push('0');
    } else {
        let mut tmp: Vec<char> = Vec::new();
        let mut rr = r_val;
        let mut k2: usize = 0;
        while (rr > 0) && (k2 < 128)
            invariant
                k2 <= 128,
                ValidBitString(tmp@),
            decreases (128 - k2) as int
        {
            let br = rr & 1u128;
            tmp.push(if br == 1u128 { '1' } else { '0' });
            rr >>= 1;
            k2 += 1;
        }
        let n2 = tmp.len();
        let mut t2: usize = 0;
        while t2 < n2
            invariant
                t2 <= n2,
                ValidBitString(r_out@),
            decreases (n2 - t2) as int
        {
            let idx2 = n2 - 1 - t2;
            let c2 = tmp[idx2];
            r_out.push(c2);
            t2 += 1;
        }
    }

    proof { assert(ValidBitString(q_out@)); }
    proof { assert(ValidBitString(r_out@)); }
    (q_out, r_out)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): safe modular exponent with explicit nonzero modulus branch, correct loop measures/invariants, and non in-place reverse */
    let mut x: u128 = 0;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases (sx.len() - i) as int
    {
        let bit = if sx[i] == '1' { 1u128 } else { 0u128 };
        x = x.wrapping_mul(2).wrapping_add(bit);
        i += 1;
    }
    let mut y: u128 = 0;
    let mut j: usize = 0;
    while j < sy.len()
        invariant
            j <= sy.len(),
        decreases (sy.len() - j) as int
    {
        let bit = if sy[j] == '1' { 1u128 } else { 0u128 };
        y = y.wrapping_mul(2).wrapping_add(bit);
        j += 1;
    }
    let mut m: u128 = 0;
    let mut k0: usize = 0;
    while k0 < sz.len()
        invariant
            k0 <= sz.len(),
        decreases (sz.len() - k0) as int
    {
        let bit = if sz[k0] == '1' { 1u128 } else { 0u128 };
        m = m.wrapping_mul(2).wrapping_add(bit);
        k0 += 1;
    }

    if m == 0 {
        let mut zero_v: Vec<char> = Vec::new();
        zero_v.push('0');
        proof { assert(ValidBitString(zero_v@)); }
        return zero_v;
    }

    let modulus: u128 = m;
    let mut base: u128 = x % modulus;
    let mut exp: u128 = y;
    let mut acc: u128 = 1 % modulus;

    let mut k: usize = 0;
    while (exp > 0) && (k < 128)
        invariant
            k <= 128,
        decreases (128 - k) as int
    {
        if (exp & 1u128) == 1u128 {
            acc = acc.wrapping_mul(base) % modulus;
        }
        base = base.wrapping_mul(base) % modulus;
        exp >>= 1;
        k += 1;
    }

    if acc == 0 {
        let mut z: Vec<char> = Vec::new();
        z.push('0');
        proof { assert(ValidBitString(z@)); }
        return z;
    }

    let mut tmp: Vec<char> = Vec::new();
    let mut tval: u128 = acc;
    let mut k2: usize = 0;
    while (tval > 0) && (k2 < 128)
        invariant
            k2 <= 128,
            ValidBitString(tmp@),
        decreases (128 - k2) as int
    {
        let b = tval & 1u128;
        tmp.push(if b == 1u128 { '1' } else { '0' });
        tval >>= 1;
        k2 += 1;
    }

    let n = tmp.len();
    let mut out: Vec<char> = Vec::new();
    let mut t: usize = 0;
    while t < n
        invariant
            t <= n,
            ValidBitString(out@),
        decreases (n - t) as int
    {
        let idx = n - 1 - t;
        let c = tmp[idx];
        out.push(c);
        t += 1;
    }

    proof { assert(ValidBitString(out@)); }
    out
}
// </vc-code>

fn main() {}
}


