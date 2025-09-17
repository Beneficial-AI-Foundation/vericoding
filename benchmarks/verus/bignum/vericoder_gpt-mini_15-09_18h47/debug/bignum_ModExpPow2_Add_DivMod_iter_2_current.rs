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
    /* code modified by LLM (iteration 2): use runtime lengths and runtime integer types (u128/usize) and avoid ghost-only length expressions */
    let len1 = s1.len() as int;
    let len2 = s2.len() as int;

    // parse s1 into v1 (runtime u128)
    let mut v1: u128 = 0;
    let mut i: int = 0;
    while i < len1
        invariant
            0 <= i && i <= len1,
        decreases len1 - i
    {
        let b = if s1[i as usize] == '1' { 1u128 } else { 0u128 };
        v1 = v1 * 2 + b;
        i = i + 1;
    }

    // parse s2 into v2 (runtime u128)
    let mut v2: u128 = 0;
    i = 0;
    while i < len2
        invariant
            0 <= i && i <= len2,
        decreases len2 - i
    {
        let b = if s2[i as usize] == '1' { 1u128 } else { 0u128 };
        v2 = v2 * 2 + b;
        i = i + 1;
    }

    // numeric sum
    let mut sum: u128 = v1 + v2;

    // convert sum to binary (LSB-first into tmp), then reverse to MSB-first
    let mut tmp = Vec::<char>::new();
    if sum == 0 {
        // represent zero by empty sequence
    } else {
        while sum > 0
            invariant
                sum >= 0u128,
            decreases sum as int
        {
            let bit = if sum % 2u128 == 1u128 { '1' } else { '0' };
            tmp.push(bit);
            sum = sum / 2u128;
        }
    }

    let mut res = Vec::<char>::new();
    let mut t: int = 0;
    let tmp_len = tmp.len() as int;
    while t < tmp_len
        invariant
            0 <= t && t <= tmp_len,
        decreases tmp_len - t
    {
        res.push(tmp[(tmp_len - 1 - t) as usize]);
        t = t + 1;
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
    /* code modified by LLM (iteration 2): parse dividend/divisor to runtime integers and convert quotient/remainder to bit vectors */
    // parse dividend
    let len_dv = dividend.len() as int;
    let mut dv_val: u128 = 0;
    let mut i: int = 0;
    while i < len_dv
        invariant
            0 <= i && i <= len_dv,
        decreases len_dv - i
    {
        let b = if dividend[i as usize] == '1' { 1u128 } else { 0u128 };
        dv_val = dv_val * 2u128 + b;
        i = i + 1;
    }

    // parse divisor
    let len_ds = divisor.len() as int;
    let mut ds_val: u128 = 0;
    i = 0;
    while i < len_ds
        invariant
            0 <= i && i <= len_ds,
        decreases len_ds - i
    {
        let b = if divisor[i as usize] == '1' { 1u128 } else { 0u128 };
        ds_val = ds_val * 2u128 + b;
        i = i + 1;
    }

    // compute quotient and remainder (runtime u128)
    let q_val: u128 = dv_val / ds_val;
    let r_val: u128 = dv_val % ds_val;

    // helper to convert u128 to Vec<char> (MSB-first)
    fn to_bits(mut x: u128) -> Vec<char> {
        let mut tmp = Vec::<char>::new();
        if x == 0 {
            return Vec::<char>::new();
        }
        while x > 0
            invariant x >= 0u128,
            decreases x as int
        {
            let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
            tmp.push(bit);
            x = x / 2u128;
        }
        let mut out = Vec::<char>::new();
        let mut t: int = 0;
        let tmp_len = tmp.len() as int;
        while t < tmp_len
            invariant 0 <= t && t <= tmp_len,
            decreases tmp_len - t
        {
            out.push(tmp[(tmp_len - 1 - t) as usize]);
            t = t + 1;
        }
        out
    }

    let q_vec = to_bits(q_val);
    let r_vec = to_bits(r_val);
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
    /* code modified by LLM (iteration 2): parse inputs to runtime integers and perform repeated squaring modulo m where exponent is 0 or 2^n */
    // parse sx into base
    let len_x = sx.len() as int;
    let mut base: u128 = 0;
    let mut i: int = 0;
    while i < len_x
        invariant
            0 <= i && i <= len_x,
        decreases len_x - i
    {
        let b = if sx[i as usize] == '1' { 1u128 } else { 0u128 };
        base = base * 2u128 + b;
        i = i + 1;
    }

    // parse sy into sy_val
    let len_y = sy.len() as int;
    let mut sy_val: u128 = 0;
    i = 0;
    while i < len_y
        invariant
            0 <= i && i <= len_y,
        decreases len_y - i
    {
        let b = if sy[i as usize] == '1' { 1u128 } else { 0u128 };
        sy_val = sy_val * 2u128 + b;
        i = i + 1;
    }

    // parse modulus sz into m
    let len_m = sz.len() as int;
    let mut m: u128 = 0;
    i = 0;
    while i < len_m
        invariant
            0 <= i && i <= len_m,
        decreases len_m - i
    {
        let b = if sz[i as usize] == '1' { 1u128 } else { 0u128 };
        m = m * 2u128 + b;
        i = i + 1;
    }

    // compute modular exponentiation where exponent is either 0 or 2^n
    let mut acc: u128;
    if sy_val == 0u128 {
        acc = 1u128 % m;
    } else {
        // start with base mod m
        acc = base % m;
        let mut k: int = 0;
        while k < n
            invariant
                0 <= k && k <= n,
            decreases n - k
        {
            acc = (acc * acc) % m;
            k = k + 1;
        }
    }

    // convert acc to bits (MSB-first)
    let mut tmp = Vec::<char>::new();
    if acc == 0u128 {
        return Vec::<char>::new();
    }
    let mut x = acc;
    while x > 0
        invariant x >= 0u128,
        decreases x as int
    {
        let bit = if x % 2u128 == 1u128 { '1' } else { '0' };
        tmp.push(bit);
        x = x / 2u128;
    }
    let mut res = Vec::<char>::new();
    let mut t: int = 0;
    let tmp_len = tmp.len() as int;
    while t < tmp_len
        invariant
            0 <= t && t <= tmp_len,
        decreases tmp_len - t
    {
        res.push(tmp[(tmp_len - 1 - t) as usize]);
        t = t + 1;
    }

    res
}

// </vc-code>

fn main() {}
}


