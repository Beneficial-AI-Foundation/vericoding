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
    /* code modified by LLM (iteration 3): avoid reverse() by manual reversal */
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut carry: u8 = 0;
    let mut rev: Vec<char> = Vec::new();

    while i > 0 || j > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            rev@.len() <= s1@.len() + s2@.len() + 1,
            forall |k: int| 0 <= k && k < rev@.len() as int ==> (rev@.index(k) == '0' || rev@.index(k) == '1'),
        decreases (i + j) as int
    {
        let a: u8 = if i > 0 && s1[i - 1] == '1' { 1 } else { 0 };
        let b: u8 = if j > 0 && s2[j - 1] == '1' { 1 } else { 0 };
        let sum: u8 = a + b + carry;
        rev.push(if (sum & 1) == 1 { '1' } else { '0' });
        carry = if sum >= 2 { 1 } else { 0 };
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    if carry > 0 { rev.push('1'); }

    let mut out: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    while idx < rev.len()
        invariant
            idx <= rev.len(),
            forall |t: int| 0 <= t && t < out@.len() as int ==> (out@.index(t) == '0' || out@.index(t) == '1'),
        decreases (rev.len() - idx) as int
    {
        out.push(rev[rev.len() - 1 - idx]);
        idx += 1;
    }
    out
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): keep shift-and-add; no reverse() used */
    // Check if either operand is zero
    let mut zero1 = true;
    let mut idx1: usize = 0;
    while idx1 < s1.len()
        invariant
            idx1 <= s1.len(),
        decreases (s1.len() - idx1) as int
    {
        if s1[idx1] == '1' { zero1 = false; }
        idx1 += 1;
    }
    let mut zero2 = true;
    let mut idx2: usize = 0;
    while idx2 < s2.len()
        invariant
            idx2 <= s2.len(),
        decreases (s2.len() - idx2) as int
    {
        if s2[idx2] == '1' { zero2 = false; }
        idx2 += 1;
    }
    if zero1 || zero2 {
        let mut z = Vec::new();
        z.push('0');
        return z;
    }

    let mut res: Vec<char> = Vec::new();
    res.push('0');

    let mut k: usize = 0;
    while k < s2.len()
        invariant
            k <= s2.len(),
            forall |t: int| 0 <= t && 0 <= t && t < res@.len() as int ==> (res@.index(t) == '0' || res@.index(t) == '1'),
        decreases (s2.len() - k) as int
    {
        let bit_index = s2.len() - 1 - k;
        if s2[bit_index] == '1' {
            let mut current: Vec<char> = Vec::new();
            // copy s1
            let mut p: usize = 0;
            while p < s1.len()
                invariant
                    p <= s1.len(),
                decreases (s1.len() - p) as int
            {
                current.push(s1[p]);
                p += 1;
            }
            // left shift by k (append k zeros)
            let mut zc: usize = 0;
            while zc < k
                invariant
                    zc <= k,
                decreases (k - zc) as int
            {
                current.push('0');
                zc += 1;
            }
            res = Add(&res, &current);
        }
        k += 1;
    }
    res
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed reverse() and used bounded decreases for bit extraction */
    // Parse sx into u128
    let mut x: u128 = 0;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases (sx.len() - i) as int
    {
        x = x.wrapping_shl(1);
        if sx[i] == '1' { x = x.wrapping_add(1); }
        i += 1;
    }

    // Parse sz into u128 (modulus)
    let mut z: u128 = 0;
    let mut j: usize = 0;
    while j < sz.len()
        invariant
            j <= sz.len(),
        decreases (sz.len() - j) as int
    {
        z = z.wrapping_shl(1);
        if sz[j] == '1' { z = z.wrapping_add(1); }
        j += 1;
    }

    // Determine if sy is zero
    let mut all_zero = true;
    let mut k: usize = 0;
    while k < sy.len()
        invariant
            k <= sy.len(),
        decreases (sy.len() - k) as int
    {
        if sy[k] == '1' { all_zero = false; }
        k += 1;
    }

    // Compute modular exponent with exponent either 0 or 2^n
    let val: u128;
    if all_zero {
        // x^0 % z == 1 % z
        val = if z == 0 { 0 } else { 1 % z };
    } else {
        // exponent is 2^n: repeated squaring n times
        let mut base = if z == 0 { 0 } else { x % z };
        // number of squarings equals n, and sy.len() == n + 1 by spec
        let n_usize: usize = if sy.len() == 0 { 0 } else { sy.len() - 1 };
        let mut t: usize = 0;
        while t < n_usize
            invariant
                t <= n_usize,
            decreases (n_usize - t) as int
        {
            let sq = base.wrapping_mul(base);
            base = if z == 0 { 0 } else { sq % z };
            t += 1;
        }
        val = base;
    }

    // Encode val into binary Vec<char> (MSB-first)
    let mut rev: Vec<char> = Vec::new();
    if val == 0 {
        rev.push('0');
    } else {
        let mut tmp = val;
        let mut count: usize = 0;
        while tmp > 0 && count < 128
            invariant
                count <= 128,
                forall |t: int| 0 <= t && t < rev@.len() as int ==> (rev@.index(t) == '0' || rev@.index(t) == '1'),
            decreases (128 - count) as int
        {
            let bit = (tmp & 1) as u8;
            rev.push(if bit == 1 { '1' } else { '0' });
            tmp >>= 1;
            count += 1;
        }
    }

    let mut out: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    while idx < rev.len()
        invariant
            idx <= rev.len(),
            forall |t: int| 0 <= t && t < out@.len() as int ==> (out@.index(t) == '0' || out@.index(t) == '1'),
        decreases (rev.len() - idx) as int
    {
        out.push(rev[rev.len() - 1 - idx]);
        idx += 1;
    }
    out
}
// </vc-code>

fn main() {}
}
