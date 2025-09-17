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
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    // Compute dividend as nat
    let mut i: int = 0;
    let mut dividend_int: nat = 0;
    while i < dividend.len() as int
        invariant
            0 <= i && i <= dividend.len() as int,
            dividend_int == (if i == 0 { 0 } else { Str2Int(dividend@.subrange(0, i as int - 1)) }),
        decreases dividend.len() as int - i
    {
        let c = dividend[i as usize];
        if c == '1' {
            dividend_int = 2 * dividend_int + 1;
        } else {
            dividend_int = 2 * dividend_int;
        }
        i += 1;
    }

    // Compute divisor as nat
    let mut j: int = 0;
    let mut divisor_int: nat = 0;
    while j < divisor.len() as int
        invariant
            0 <= j && j <= divisor.len() as int,
            divisor_int == (if j == 0 { 0 } else { Str2Int(divisor@.subrange(0, j as int - 1)) }),
        decreases divisor.len() as int - j
    {
        let c = divisor[j as usize];
        if c == '1' {
            divisor_int = 2 * divisor_int + 1;
        } else {
            divisor_int = 2 * divisor_int;
        }
        j += 1;
    }

    // Compute quotient and remainder as nats
    let quot_nat: nat = dividend_int / divisor_int;
    let rem_nat: nat = dividend_int % divisor_int;

    // Convert nat -> Vec<char> (MSB-first) for quotient
    let mut q_vec: Vec<char> = Vec::new();
    if quot_nat != 0 {
        let mut tmp: Vec<char> = Vec::new(); // LSB-first
        let mut vq: nat = quot_nat;
        while vq > 0
            invariant
                vq >= 0,
            decreases vq
        {
            if vq % 2 == 1 { tmp.push('1'); } else { tmp.push('0'); }
            vq = vq / 2;
        }
        let mut k: int = tmp.len() as int;
        while k > 0
            invariant
                0 <= k && k <= tmp.len() as int,
            decreases k
        {
            k -= 1;
            q_vec.push(tmp[k as usize]);
        }
    }

    // Convert nat -> Vec<char> (MSB-first) for remainder
    let mut r_vec: Vec<char> = Vec::new();
    if rem_nat != 0 {
        let mut tmp2: Vec<char> = Vec::new();
        let mut vr: nat = rem_nat;
        while vr > 0
            invariant
                vr >= 0,
            decreases vr
        {
            if vr % 2 == 1 { tmp2.push('1'); } else { tmp2.push('0'); }
            vr = vr / 2;
        }
        let mut kk: int = tmp2.len() as int;
        while kk > 0
            invariant
                0 <= kk && kk <= tmp2.len() as int,
            decreases kk
        {
            kk -= 1;
            r_vec.push(tmp2[kk as usize]);
        }
    }

    return (q_vec, r_vec);
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
    // Compute sx as nat
    let mut i: int = 0;
    let mut sx_int: nat = 0;
    while i < sx.len() as int
        invariant
            0 <= i && i <= sx.len() as int,
            sx_int == (if i == 0 { 0 } else { Str2Int(sx@.subrange(0, i as int - 1)) }),
        decreases sx.len() as int - i
    {
        let c = sx[i as usize];
        if c == '1' {
            sx_int = 2 * sx_int + 1;
        } else {
            sx_int = 2 * sx_int;
        }
        i += 1;
    }

    // Compute sy as nat
    let mut j: int = 0;
    let mut sy_int: nat = 0;
    while j < sy.len() as int
        invariant
            0 <= j && j <= sy.len() as int,
            sy_int == (if j == 0 { 0 } else { Str2Int(sy@.subrange(0, j as int - 1)) }),
        decreases sy.len() as int - j
    {
        let c = sy[j as usize];
        if c == '1' {
            sy_int = 2 * sy_int + 1;
        } else {
            sy_int = 2 * sy_int;
        }
        j += 1;
    }

    // Compute sz as nat
    let mut k: int = 0;
    let mut sz_int: nat = 0;
    while k < sz.len() as int
        invariant
            0 <= k && k <= sz.len() as int,
            sz_int == (if k == 0 { 0 } else { Str2Int(sz@.subrange(0, k as int - 1)) }),
        decreases sz.len() as int - k
    {
        let c = sz[k as usize];
        if c == '1' {
            sz_int = 2 * sz_int + 1;
        } else {
            sz_int = 2 * sz_int;
        }
        k += 1;
    }

    // Compute result integer
    let mut result_int: nat;
    if sy_int == 0 {
        // x^0 == 1
        result_int = 1 % sz_int;
    } else {
        // sy_int == 2^n by spec; repeated squaring n times
        let mut acc: nat = sx_int % sz_int;
        let mut t: int = 0;
        while t < n
            invariant
                0 <= t && t <= n,
            decreases n - t
        {
            acc = (acc * acc) % sz_int;
            t += 1;
        }
        result_int = acc;
    }

    // Convert result_int to Vec<char> (MSB-first)
    let mut res_vec: Vec<char> = Vec::new();
    if result_int != 0 {
        let mut tmp: Vec<char> = Vec::new();
        let mut v: nat = result_int;
        while v > 0
            invariant
                v >= 0,
            decreases v
        {
            if v % 2 == 1 { tmp.push('1'); } else { tmp.push('0'); }
            v = v / 2;
        }
        let mut p: int = tmp.len() as int;
        while p > 0
            invariant
                0 <= p && p <= tmp.len() as int,
            decreases p
        {
            p -= 1;
            res_vec.push(tmp[p as usize]);
        }
    }

    return res_vec;
}
// </vc-code>

fn main() {}
}


