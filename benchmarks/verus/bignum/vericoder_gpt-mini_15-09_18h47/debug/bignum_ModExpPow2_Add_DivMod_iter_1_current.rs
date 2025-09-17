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
    let len1 = s1@.len() as int;
    let len2 = s2@.len() as int;

    // parse s1 into v1
    let mut v1: nat = 0;
    let mut i: int = 0;
    while i < len1
        invariant
            0 <= i && i <= len1,
            v1 == Str2Int(s1@.subrange(0, i)),
        decreases len1 - i
    {
        let b = if s1@.index(i) == '1' { 1 } else { 0 };
        v1 = v1 * 2 + b;
        i = i + 1;
    }

    // parse s2 into v2
    let mut v2: nat = 0;
    i = 0;
    while i < len2
        invariant
            0 <= i && i <= len2,
            v2 == Str2Int(s2@.subrange(0, i)),
        decreases len2 - i
    {
        let b = if s2@.index(i) == '1' { 1 } else { 0 };
        v2 = v2 * 2 + b;
        i = i + 1;
    }

    // numeric sum
    let mut sum = v1 + v2;

    // convert sum to binary (LSB-first into tmp), then reverse to MSB-first
    let mut tmp = Vec::<char>::new();
    if sum == 0 {
        // represent zero by empty sequence (Str2Int(empty) == 0)
    } else {
        while sum > 0
            invariant
                sum >= 0,
            decreases sum
        {
            let bit = if sum % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            sum = sum / 2;
        }
    }

    let mut res = Vec::<char>::new();
    let mut t: int = 0;
    let tmp_len = tmp@.len() as int;
    while t < tmp_len
        invariant
            0 <= t && t <= tmp_len,
            res@.len() as int == t,
        decreases tmp_len - t
    {
        res.push(tmp@.index(tmp_len - 1 - t));
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
    // parse dividend
    let len_dv = dividend@.len() as int;
    let mut dv_val: nat = 0;
    let mut i: int = 0;
    while i < len_dv
        invariant
            0 <= i && i <= len_dv,
            dv_val == Str2Int(dividend@.subrange(0, i)),
        decreases len_dv - i
    {
        let b = if dividend@.index(i) == '1' { 1 } else { 0 };
        dv_val = dv_val * 2 + b;
        i = i + 1;
    }

    // parse divisor
    let len_ds = divisor@.len() as int;
    let mut ds_val: nat = 0;
    i = 0;
    while i < len_ds
        invariant
            0 <= i && i <= len_ds,
            ds_val == Str2Int(divisor@.subrange(0, i)),
        decreases len_ds - i
    {
        let b = if divisor@.index(i) == '1' { 1 } else { 0 };
        ds_val = ds_val * 2 + b;
        i = i + 1;
    }

    // compute quotient and remainder
    let q_val: nat = dv_val / ds_val;
    let r_val: nat = dv_val % ds_val;

    // helper to convert nat to Vec<char> (MSB-first)
    fn to_bits(mut x: nat) -> Vec<char> {
        let mut tmp = Vec::<char>::new();
        if x == 0 {
            return Vec::<char>::new();
        }
        while x > 0
            invariant x >= 0,
            decreases x
        {
            let bit = if x % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            x = x / 2;
        }
        let mut out = Vec::<char>::new();
        let mut t: int = 0;
        let tmp_len = tmp@.len() as int;
        while t < tmp_len
            invariant 0 <= t && t <= tmp_len, out@.len() as int == t,
            decreases tmp_len - t
        {
            out.push(tmp@.index(tmp_len - 1 - t));
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
    // parse sx into base
    let len_x = sx@.len() as int;
    let mut base: nat = 0;
    let mut i: int = 0;
    while i < len_x
        invariant
            0 <= i && i <= len_x,
            base == Str2Int(sx@.subrange(0, i)),
        decreases len_x - i
    {
        let b = if sx@.index(i) == '1' { 1 } else { 0 };
        base = base * 2 + b;
        i = i + 1;
    }

    // parse sy into sy_val
    let len_y = sy@.len() as int;
    let mut sy_val: nat = 0;
    i = 0;
    while i < len_y
        invariant
            0 <= i && i <= len_y,
            sy_val == Str2Int(sy@.subrange(0, i)),
        decreases len_y - i
    {
        let b = if sy@.index(i) == '1' { 1 } else { 0 };
        sy_val = sy_val * 2 + b;
        i = i + 1;
    }

    // parse modulus sz into m
    let len_m = sz@.len() as int;
    let mut m: nat = 0;
    i = 0;
    while i < len_m
        invariant
            0 <= i && i <= len_m,
            m == Str2Int(sz@.subrange(0, i)),
        decreases len_m - i
    {
        let b = if sz@.index(i) == '1' { 1 } else { 0 };
        m = m * 2 + b;
        i = i + 1;
    }

    // compute modular exponentiation where exponent is either 0 or 2^n
    let mut acc: nat;
    if sy_val == 0 {
        acc = 1 % m;
    } else {
        // start with base mod m
        acc = base % m;
        let mut k: int = 0;
        while k < n
            invariant
                0 <= k && k <= n,
                acc < m,
            decreases n - k
        {
            acc = (acc * acc) % m;
            k = k + 1;
        }
    }

    // convert acc to bits (MSB-first)
    let mut tmp = Vec::<char>::new();
    if acc == 0 {
        return Vec::<char>::new();
    }
    let mut x = acc;
    while x > 0
        invariant x >= 0,
        decreases x
    {
        let bit = if x % 2 == 1 { '1' } else { '0' };
        tmp.push(bit);
        x = x / 2;
    }
    let mut res = Vec::<char>::new();
    let mut t: int = 0;
    let tmp_len = tmp@.len() as int;
    while t < tmp_len
        invariant
            0 <= t && t <= tmp_len,
            res@.len() as int == t,
        decreases tmp_len - t
    {
        res.push(tmp@.index(tmp_len - 1 - t));
        t = t + 1;
    }

    res
}
// </vc-code>

fn main() {}
}


