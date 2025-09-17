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
    /* code modified by LLM (iteration 8): compute values as u128 and return sum bits MSB-first */
    let len1 = s1.len();
    let len2 = s2.len();

    let mut v1: u128 = 0;
    let mut i: usize = 0;
    while i < len1
        invariant
            i <= len1,
        decreases len1 - i
    {
        let b = if s1[i] == '1' { 1u128 } else { 0u128 };
        v1 = v1 * 2u128 + b;
        i += 1;
    }

    let mut v2: u128 = 0;
    i = 0;
    while i < len2
        invariant
            i <= len2,
        decreases len2 - i
    {
        let b = if s2[i] == '1' { 1u128 } else { 0u128 };
        v2 = v2 * 2u128 + b;
        i += 1;
    }

    let mut sum: u128 = v1 + v2;

    let mut tmp = Vec::<char>::new();
    if sum == 0u128 {
        // represent zero by empty sequence
    } else {
        while sum > 0u128
            invariant
                sum >= 0u128,
            decreases (sum as usize)
        {
            let bit = if sum % 2u128 == 1u128 { '1' } else { '0' };
            tmp.push(bit);
            sum = sum / 2u128;
        }
    }

    let mut res = Vec::<char>::new();
    let mut t: usize = 0;
    let tmp_len = tmp.len();
    while t < tmp_len
        invariant
            t <= tmp_len,
        decreases tmp_len - t
    {
        res.push(tmp[tmp_len - 1 - t]);
        t += 1;
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
    /* code modified by LLM (iteration 8): parse dividend/divisor into u128 and convert quotient/remainder to bit vectors */
    let len_dv = dividend.len();
    let mut dv_val: u128 = 0;
    let mut i: usize = 0;
    while i < len_dv
        invariant
            i <= len_dv,
        decreases len_dv - i
    {
        let b = if dividend[i] == '1' { 1u128 } else { 0u128 };
        dv_val = dv_val * 2u128 + b;
        i += 1;
    }

    let len_ds = divisor.len();
    let mut ds_val: u128 = 0;
    i = 0;
    while i < len_ds
        invariant
            i <= len_ds,
        decreases len_ds - i
    {
        let b = if divisor[i] == '1' { 1u128 } else { 0u128 };
        ds_val = ds_val * 2u128 + b;
        i += 1;
    }

    let q_val: u128 = dv_val / ds_val;
    let r_val: u128 = dv_val % ds_val;

    // convert q_val to bits (MSB-first)
    let mut tmp_q = Vec::<char>::new();
    if q_val == 0u128 {
        // empty for zero
    } else {
        let mut x = q_val;
        while x > 0u128
            invariant
                x >= 0u128,
            decreases (x as usize)
        {
            let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
            tmp_q.push(bit);
            x = x / 2u128;
        }
    }
    let mut q_vec = Vec::<char>::new();
    let mut t: usize = 0;
    let tmp_q_len = tmp_q.len();
    while t < tmp_q_len
        invariant
            t <= tmp_q_len,
        decreases tmp_q_len - t
    {
        q_vec.push(tmp_q[tmp_q_len - 1 - t]);
        t += 1;
    }

    // convert r_val to bits (MSB-first)
    let mut tmp_r = Vec::<char>::new();
    if r_val == 0u128 {
        // empty for zero
    } else {
        let mut x = r_val;
        while x > 0u128
            invariant
                x >= 0u128,
            decreases (x as usize)
        {
            let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
            tmp_r.push(bit);
            x = x / 2u128;
        }
    }
    let mut r_vec = Vec::<char>::new();
    t = 0;
    let tmp_r_len = tmp_r.len();
    while t < tmp_r_len
        invariant
            t <= tmp_r_len,
        decreases tmp_r_len - t
    {
        r_vec.push(tmp_r[tmp_r_len - 1 - t]);
        t += 1;
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
    /* code modified by LLM (iteration 8): compute base and modulus, perform n squarings using usize loop counter and return result bits MSB-first */
    let len_x = sx.len();
    let mut base: u128 = 0;
    let mut i: usize = 0;
    while i < len_x
        invariant
            i <= len_x,
        decreases len_x - i
    {
        let b = if sx[i] == '1' { 1u128 } else { 0u128 };
        base = base * 2u128 + b;
        i += 1;
    }

    let len_y = sy.len();
    let mut sy_val: u128 = 0;
    i = 0;
    while i < len_y
        invariant
            i <= len_y,
        decreases len_y - i
    {
        let b = if sy[i] == '1' { 1u128 } else { 0u128 };
        sy_val = sy_val * 2u128 + b;
        i += 1;
    }

    let len_m = sz.len();
    let mut m: u128 = 0;
    i = 0;
    while i < len_m
        invariant
            i <= len_m,
        decreases len_m - i
    {
        let b = if sz[i] == '1' { 1u128 } else { 0u128 };
        m = m * 2u128 + b;
        i += 1;
    }

    let mut acc: u128;
    if sy_val == 0u128 {
        acc = 1u128 % m;
    } else {
        acc = base % m;
        let nn: usize = if n >= 0 { n as usize } else { 0usize };
        let mut k: usize = 0;
        while k < nn
            invariant
                k <= nn,
            decreases nn - k
        {
            acc = (acc * acc) % m;
            k = k + 1;
        }
    }

    let mut tmp = Vec::<char>::new();
    if acc == 0u128 {
        return Vec::<char>::new();
    }
    let mut x = acc;
    while x > 0u128
        invariant
            x >= 0u128,
        decreases (x as usize)
    {
        let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
        tmp.push(bit);
        x = x / 2u128;
    }
    let mut res = Vec::<char>::new();
    let mut t: usize = 0;
    let tmp_len = tmp.len();
    while t < tmp_len
        invariant
            t <= tmp_len,
        decreases tmp_len - t
    {
        res.push(tmp[tmp_len - 1 - t]);
        t += 1;
    }

    res
}
// </vc-code>

fn main() {}
}


