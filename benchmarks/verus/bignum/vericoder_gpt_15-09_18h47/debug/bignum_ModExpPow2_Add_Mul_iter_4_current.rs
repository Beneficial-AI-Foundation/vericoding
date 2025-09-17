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
    /* code modified by LLM (iteration 4): binary string addition without reverse() intrinsic */
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
        rev.push(if (sum % 2) == 1 { '1' } else { '0' });
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
    /* code modified by LLM (iteration 4): shift-and-add multiplication using Add; avoids reverse() */
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
            forall |t: int| 0 <= t && t < res@.len() as int ==> (res@.index(t) == '0' || res@.index(t) == '1'),
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
    /* code modified by LLM (iteration 4): removed wrapping_shl/mul and used safe modular multiplication via doubling */
    // Parse sx into u128
    let mut x: u128 = 0;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases (sx.len() - i) as int
    {
        x = x << 1;
        if sx[i] == '1' { x = x + 1; }
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
        z = z << 1;
        if sz[j] == '1' { z = z + 1; }
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
        if z == 0 {
            val = 0;
        } else {
            // exponent is 2^n: repeated squaring n times
            let mut base = x % z;
            // number of squarings equals n, and sy.len() == n + 1 by spec
            let n_usize: usize = if sy.len() == 0 { 0 } else { sy.len() - 1 };
            let mut t: usize = 0;
            while t < n_usize
                invariant
                    t <= n_usize,
                decreases (n_usize - t) as int
            {
                // base = (base * base) % z using modular multiplication without overflow
                let mut res_mul: u128 = 0;
                let mut addend: u128 = base % z;
                let mut yy: u128 = base;
                let mut steps: usize = 0;
                while yy > 0 && steps < 128
                    invariant
                        steps <= 128,
                    decreases (128 - steps) as int
                {
                    if yy % 2 == 1 {
                        // res_mul = (res_mul + addend) % z without overflow
                        if res_mul >= z - addend {
                            res_mul = res_mul - (z - addend);
                        } else {
                            res_mul = res_mul + addend;
                        }
                    }
                    // addend = (addend + addend) % z without overflow
                    if addend >= z - addend {
                        addend = addend - (z - addend);
                    } else {
                        addend = addend + addend;
                    }
                    yy /= 2;
                    steps += 1;
                }
                base = res_mul;
                t += 1;
            }
            val = base;
        }
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
                forall |t2: int| 0 <= t2 && t2 < rev@.len() as int ==> (rev@.index(t2) == '0' || rev@.index(t2) == '1'),
            decreases (128 - count) as int
        {
            let bit = (tmp % 2) as u8;
            rev.push(if bit == 1 { '1' } else { '0' });
            tmp /= 2;
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
