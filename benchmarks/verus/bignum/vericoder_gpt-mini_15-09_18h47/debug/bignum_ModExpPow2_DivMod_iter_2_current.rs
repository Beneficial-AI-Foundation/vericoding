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
    /* code modified by LLM (iteration 2): use usize counters and tracked nats to avoid int/nat in non-ghost context */

    // Compute dividend as nat (tracked)
    let mut i: usize = 0;
    let mut tracked dividend_int: nat = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            dividend_int == Str2Int(dividend@.subrange(0, i as int)),
        decreases dividend.len() - i
    {
        let c = dividend[i];
        if c == '1' {
            dividend_int = 2 * dividend_int + 1;
        } else {
            dividend_int = 2 * dividend_int;
        }
        i += 1;
    }

    // Compute divisor as nat (tracked)
    let mut j: usize = 0;
    let mut tracked divisor_int: nat = 0;
    while j < divisor.len()
        invariant
            j <= divisor.len(),
            divisor_int == Str2Int(divisor@.subrange(0, j as int)),
        decreases divisor.len() - j
    {
        let c = divisor[j];
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
        let mut tracked vq: nat = quot_nat;
        while vq > 0
            invariant
                vq >= 0,
            decreases vq
        {
            if vq % 2 == 1 { tmp.push('1'); } else { tmp.push('0'); }
            vq = vq / 2;
        }
        let mut k: usize = tmp.len();
        while k > 0
            invariant
                k <= tmp.len(),
            decreases k
        {
            k -= 1;
            q_vec.push(tmp[k]);
        }
    }

    // Convert nat -> Vec<char> (MSB-first) for remainder
    let mut r_vec: Vec<char> = Vec::new();
    if rem_nat != 0 {
        let mut tmp2: Vec<char> = Vec::new();
        let mut tracked vr: nat = rem_nat;
        while vr > 0
            invariant
                vr >= 0,
            decreases vr
        {
            if vr % 2 == 1 { tmp2.push('1'); } else { tmp2.push('0'); }
            vr = vr / 2;
        }
        let mut kk: usize = tmp2.len();
        while kk > 0
            invariant
                kk <= tmp2.len(),
            decreases kk
        {
            kk -= 1;
            r_vec.push(tmp2[kk]);
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
    /* code modified by LLM (iteration 2): use usize counters and tracked nats; cast n to usize for loops */

    // Compute sx as nat (tracked)
    let mut i: usize = 0;
    let mut tracked sx_int: nat = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
            sx_int == Str2Int(sx@.subrange(0, i as int)),
        decreases sx.len() - i
    {
        let c = sx[i];
        if c == '1' {
            sx_int = 2 * sx_int + 1;
        } else {
            sx_int = 2 * sx_int;
        }
        i += 1;
    }

    // Compute sy as nat (tracked)
    let mut j: usize = 0;
    let mut tracked sy_int: nat = 0;
    while j < sy.len()
        invariant
            j <= sy.len(),
            sy_int == Str2Int(sy@.subrange(0, j as int)),
        decreases sy.len() - j
    {
        let c = sy[j];
        if c == '1' {
            sy_int = 2 * sy_int + 1;
        } else {
            sy_int = 2 * sy_int;
        }
        j += 1;
    }

    // Compute sz as nat (tracked)
    let mut k: usize = 0;
    let mut tracked sz_int: nat = 0;
    while k < sz.len()
        invariant
            k <= sz.len(),
            sz_int == Str2Int(sz@.subrange(0, k as int)),
        decreases sz.len() - k
    {
        let c = sz[k];
        if c == '1' {
            sz_int = 2 * sz_int + 1;
        } else {
            sz_int = 2 * sz_int;
        }
        k += 1;
    }

    // Compute result integer
    let mut tracked result_int: nat;
    if sy_int == 0 {
        // x^0 == 1
        result_int = 1 % sz_int;
    } else {
        // sy_int == 2^n by spec; repeated squaring n times
        let mut acc: nat = sx_int % sz_int;
        let n_usize: usize = if n >= 0 { n as usize } else { 0usize };
        let mut t: usize = 0;
        while t < n_usize
            invariant
                t <= n_usize,
            decreases n_usize - t
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
        let mut tracked v: nat = result_int;
        while v > 0
            invariant
                v >= 0,
            decreases v
        {
            if v % 2 == 1 { tmp.push('1'); } else { tmp.push('0'); }
            v = v / 2;
        }
        let mut p: usize = tmp.len();
        while p > 0
            invariant
                p <= tmp.len(),
            decreases p
        {
            p -= 1;
            res_vec.push(tmp[p]);
        }
    }

    return res_vec;
}
// </vc-code>

fn main() {}
}


