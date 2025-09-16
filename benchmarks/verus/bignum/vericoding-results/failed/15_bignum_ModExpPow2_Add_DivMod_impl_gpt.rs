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
    let mut res_rev: Vec<char> = Vec::new();
    let mut i: int = s1.len() as int;
    let mut j: int = s2.len() as int;
    let mut carry: int = 0;
    while i > 0 || j > 0
        invariant
            0 <= i && i <= s1.len() as int,
            0 <= j && j <= s2.len() as int,
        decreases (i + j)
    {
        let b1: int = if i > 0 && s1[(i as usize) - 1] == '1' { 1 } else { 0 };
        let b2: int = if j > 0 && s2[(j as usize) - 1] == '1' { 1 } else { 0 };
        let sum: int = b1 + b2 + carry;
        let bit: int = if sum % 2 == 0 { 0 } else { 1 };
        carry = if sum >= 2 { 1 } else { 0 };
        res_rev.push(if bit == 1 { '1' } else { '0' });
        if i > 0 { i = i - 1; }
        if j > 0 { j = j - 1; }
    }
    if carry == 1 {
        res_rev.push('1');
    }
    let mut res: Vec<char> = Vec::new();
    let mut k: int = res_rev.len() as int;
    while k > 0
        invariant
            0 <= k && k <= res_rev.len() as int,
        decreases k
    {
        res.push(res_rev[(k as usize) - 1]);
        k = k - 1;
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
    // parse dividend to int
    let mut a: int = 0;
    let mut i: int = 0;
    while i < dividend.len() as int
        invariant
            0 <= i && i <= dividend.len() as int,
        decreases (dividend.len() as int - i)
    {
        let ch = dividend[i as usize];
        a = 2 * a + if ch == '1' { 1 } else { 0 };
        i = i + 1;
    }
    // parse divisor to int
    let mut b: int = 0;
    let mut j: int = 0;
    while j < divisor.len() as int
        invariant
            0 <= j && j <= divisor.len() as int,
        decreases (divisor.len() as int - j)
    {
        let ch = divisor[j as usize];
        b = 2 * b + if ch == '1' { 1 } else { 0 };
        j = j + 1;
    }
    let q: int = if b == 0 { 0 } else { a / b };
    let r: int = if b == 0 { 0 } else { a % b };

    // build quotient vector
    let mut q_vec: Vec<char> = Vec::new();
    if q == 0 {
        q_vec.push('0');
    } else {
        let mut t: int = if q < 0 { -q } else { q }; // positive magnitude (bitstring for non-negative, but q should be >= 0 here)
        let mut rev: Vec<char> = Vec::new();
        while t > 0
            invariant
                t >= 0,
            decreases t
        {
            let bitv: int = t % 2;
            rev.push(if bitv == 1 { '1' } else { '0' });
            t = t / 2;
        }
        let mut k: int = rev.len() as int;
        while k > 0
            invariant
                0 <= k && k <= rev.len() as int,
            decreases k
        {
            q_vec.push(rev[(k as usize) - 1]);
            k = k - 1;
        }
    }

    // build remainder vector
    let mut r_vec: Vec<char> = Vec::new();
    if r == 0 {
        r_vec.push('0');
    } else {
        let mut t: int = r;
        let mut rev: Vec<char> = Vec::new();
        while t > 0
            invariant
                t >= 0,
            decreases t
        {
            let bitv: int = t % 2;
            rev.push(if bitv == 1 { '1' } else { '0' });
            t = t / 2;
        }
        let mut k: int = rev.len() as int;
        while k > 0
            invariant
                0 <= k && k <= rev.len() as int,
            decreases k
        {
            r_vec.push(rev[(k as usize) - 1]);
            k = k - 1;
        }
    }

    (q_vec, r_vec)
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
    // parse sx, sy, sz to int
    let mut x: int = 0;
    let mut i: int = 0;
    while i < sx.len() as int
        invariant
            0 <= i && i <= sx.len() as int,
        decreases (sx.len() as int - i)
    {
        let ch = sx[i as usize];
        x = 2 * x + if ch == '1' { 1 } else { 0 };
        i = i + 1;
    }
    let mut y: int = 0;
    let mut j: int = 0;
    while j < sy.len() as int
        invariant
            0 <= j && j <= sy.len() as int,
        decreases (sy.len() as int - j)
    {
        let ch = sy[j as usize];
        y = 2 * y + if ch == '1' { 1 } else { 0 };
        j = j + 1;
    }
    let mut z: int = 0;
    let mut k2: int = 0;
    while k2 < sz.len() as int
        invariant
            0 <= k2 && k2 <= sz.len() as int,
        decreases (sz.len() as int - k2)
    {
        let ch = sz[k2 as usize];
        z = 2 * z + if ch == '1' { 1 } else { 0 };
        k2 = k2 + 1;
    }
    let modulus: int = if z == 0 { 1 } else { z };

    // modular exponentiation by squaring (with non-negative values)
    let mut base: int = x % modulus; if base < 0 { base = base + modulus; }
    let mut exp: int = if y < 0 { 0 } else { y };
    let mut acc: int = 1 % modulus; if acc < 0 { acc = acc + modulus; }
    while exp > 0
        invariant
            exp >= 0,
            modulus > 0,
            0 <= acc && acc < modulus,
        decreases exp
    {
        if exp % 2 == 1 {
            acc = (acc * base) % modulus; if acc < 0 { acc = acc + modulus; }
        }
        base = (base * base) % modulus; if base < 0 { base = base + modulus; }
        exp = exp / 2;
    }
    let value: int = acc % modulus; // already in [0, modulus)

    // build result vector from value
    let mut res: Vec<char> = Vec::new();
    if value == 0 {
        res.push('0');
    } else {
        let mut t: int = value;
        let mut rev: Vec<char> = Vec::new();
        while t > 0
            invariant
                t >= 0,
            decreases t
        {
            let bitv: int = t % 2;
            rev.push(if bitv == 1 { '1' } else { '0' });
            t = t / 2;
        }
        let mut k: int = rev.len() as int;
        while k > 0
            invariant
                0 <= k && k <= rev.len() as int,
            decreases k
        {
            res.push(rev[(k as usize) - 1]);
            k = k - 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}


