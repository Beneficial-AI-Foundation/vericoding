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
    /* code modified by LLM (iteration 2): implement addition via u128 parsing, avoid casts, and fix reverse loop invariants/decreases */
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
    let mut res: Vec<char> = Vec::new();
    if sum == 0 {
        res.push('0');
        return res;
    }
    let mut k: usize = 0;
    while (sum > 0) && (k < 128)
        invariant
            k <= 128,
        decreases (128 - k) as int
    {
        let b = sum & 1u128;
        res.push(if b == 1u128 { '1' } else { '0' });
        sum >>= 1;
        k += 1;
    }
    let n = res.len();
    if n > 1 {
        let mut l: usize = 0;
        let mut r: usize = n - 1;
        while l < r
            invariant
                n == res.len(),
                l <= r,
                r < n,
            decreases (r - l) as int
        {
            let tmp = res[l];
            res[l] = res[r];
            res[r] = tmp;
            l += 1;
            r -= 1;
        }
    }
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
    /* code modified by LLM (iteration 2): implement division/modulo via u128 parsing, avoid casts, and fix reverse loop invariants/decreases */
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

    let mut q_vec: Vec<char> = Vec::new();
    if q_val == 0 {
        q_vec.push('0');
    } else {
        let mut q = q_val;
        let mut k: usize = 0;
        while (q > 0) && (k < 128)
            invariant
                k <= 128,
            decreases (128 - k) as int
        {
            let bq = q & 1u128;
            q_vec.push(if bq == 1u128 { '1' } else { '0' });
            q >>= 1;
            k += 1;
        }
        let n = q_vec.len();
        if n > 1 {
            let mut l: usize = 0;
            let mut r: usize = n - 1;
            while l < r
                invariant
                    n == q_vec.len(),
                    l <= r,
                    r < n,
                decreases (r - l) as int
            {
                let tmp = q_vec[l];
                q_vec[l] = q_vec[r];
                q_vec[r] = tmp;
                l += 1;
                r -= 1;
            }
        }
    }

    let mut r_vec: Vec<char> = Vec::new();
    if r_val == 0 {
        r_vec.push('0');
    } else {
        let mut rr = r_val;
        let mut k2: usize = 0;
        while (rr > 0) && (k2 < 128)
            invariant
                k2 <= 128,
            decreases (128 - k2) as int
        {
            let br = rr & 1u128;
            r_vec.push(if br == 1u128 { '1' } else { '0' });
            rr >>= 1;
            k2 += 1;
        }
        let n2 = r_vec.len();
        if n2 > 1 {
            let mut l2: usize = 0;
            let mut r2: usize = n2 - 1;
            while l2 < r2
                invariant
                    n2 == r_vec.len(),
                    l2 <= r2,
                    r2 < n2,
                decreases (r2 - l2) as int
            {
                let tmp = r_vec[l2];
                r_vec[l2] = r_vec[r2];
                r_vec[r2] = tmp;
                l2 += 1;
                r2 -= 1;
            }
        }
    }

    (q_vec, r_vec)
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
    /* code modified by LLM (iteration 2): implement modular exponent via square-and-multiply, avoid casts, assert nonzero modulus, and fix reverse loop invariants/decreases */
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

    let modulus: u128 = if m == 0 { 1 } else { m };
    assert(modulus != 0);

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

    let mut out: Vec<char> = Vec::new();
    if acc == 0 {
        out.push('0');
        return out;
    }
    let mut t: u128 = acc;
    let mut k2: usize = 0;
    while (t > 0) && (k2 < 128)
        invariant
            k2 <= 128,
        decreases (128 - k2) as int
    {
        let b = t & 1u128;
        out.push(if b == 1u128 { '1' } else { '0' });
        t >>= 1;
        k2 += 1;
    }
    let n = out.len();
    if n > 1 {
        let mut l: usize = 0;
        let mut r: usize = n - 1;
        while l < r
            invariant
                n == out.len(),
                l <= r,
                r < n,
            decreases (r - l) as int
        {
            let tmp = out[l];
            out[l] = out[r];
            out[r] = tmp;
            l += 1;
            r -= 1;
        }
    }
    out
}
// </vc-code>

fn main() {}
}


