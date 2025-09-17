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
    // Compute numeric value of dividend
    let len_d = dividend.len() as int;
    let mut i: int = 0;
    let mut a: nat = 0;
    while i < len_d
        invariant
            a == Str2Int(dividend@.subrange(0, i)),
        decreases len_d - i
    {
        if dividend@.index(i) == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        i += 1;
    }

    // Compute numeric value of divisor
    let len_v = divisor.len() as int;
    let mut j: int = 0;
    let mut b: nat = 0;
    while j < len_v
        invariant
            b == Str2Int(divisor@.subrange(0, j)),
        decreases len_v - j
    {
        if divisor@.index(j) == '1' {
            b = 2 * b + 1;
        } else {
            b = 2 * b;
        }
        j += 1;
    }

    // Compute quotient and remainder numerically
    let q: nat = a / b;
    let r: nat = a % b;

    // Convert q to Vec<char>
    let mut res_q: Vec<char> = Vec::new();
    if q != 0 {
        let mut pow: nat = 1;
        let mut k: int = 0;
        while pow * 2 <= q
            invariant
                pow == Exp_int(2, k as nat),
            decreases q - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut idxi: int = k;
        let mut res_val: nat = 0;
        let mut rem: nat = q;
        while idxi >= 0
            invariant
                res_val == Str2Int(res_q@),
                rem + res_val * Exp_int(2, (idxi as nat) + 1) == q,
            decreases idxi + 1
        {
            let powi = Exp_int(2, idxi as nat);
            if rem >= powi {
                res_q.push('1');
                res_val = res_val * 2 + 1;
                rem = rem - powi;
            } else {
                res_q.push('0');
                res_val = res_val * 2;
            }
            idxi -= 1;
        }
    }

    // Convert r to Vec<char>
    let mut res_r: Vec<char> = Vec::new();
    if r != 0 {
        let mut pow2: nat = 1;
        let mut k2: int = 0;
        while pow2 * 2 <= r
            invariant
                pow2 == Exp_int(2, k2 as nat),
            decreases r - pow2
        {
            pow2 = pow2 * 2;
            k2 += 1;
        }

        let mut idxr: int = k2;
        let mut res_val2: nat = 0;
        let mut rem2: nat = r;
        while idxr >= 0
            invariant
                res_val2 == Str2Int(res_r@),
                rem2 + res_val2 * Exp_int(2, (idxr as nat) + 1) == r,
            decreases idxr + 1
        {
            let powi = Exp_int(2, idxr as nat);
            if rem2 >= powi {
                res_r.push('1');
                res_val2 = res_val2 * 2 + 1;
                rem2 = rem2 - powi;
            } else {
                res_r.push('0');
                res_val2 = res_val2 * 2;
            }
            idxr -= 1;
        }
    }

    return (res_q, res_r);
}

// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Compute numeric values of s1 and s2
    let len1 = s1.len() as int;
    let mut i: int = 0;
    let mut a: nat = 0;
    while i < len1
        invariant
            a == Str2Int(s1@.subrange(0, i)),
        decreases len1 - i
    {
        if s1@.index(i) == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        i += 1;
    }

    let len2 = s2.len() as int;
    let mut j: int = 0;
    let mut b: nat = 0;
    while j < len2
        invariant
            b == Str2Int(s2@.subrange(0, j)),
        decreases len2 - j
    {
        if s2@.index(j) == '1' {
            b = 2 * b + 1;
        } else {
            b = 2 * b;
        }
        j += 1;
    }

    // Compute product
    let p: nat = a * b;

    // Convert product to Vec<char>
    let mut res: Vec<char> = Vec::new();
    if p != 0 {
        let mut pow: nat = 1;
        let mut k: int = 0;
        while pow * 2 <= p
            invariant
                pow == Exp_int(2, k as nat),
            decreases p - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut idx: int = k;
        let mut res_val: nat = 0;
        let mut rem: nat = p;
        while idx >= 0
            invariant
                res_val == Str2Int(res@),
                rem + res_val * Exp_int(2, (idx as nat) + 1) == p,
            decreases idx + 1
        {
            let powi = Exp_int(2, idx as nat);
            if rem >= powi {
                res.push('1');
                res_val = res_val * 2 + 1;
                rem = rem - powi;
            } else {
                res.push('0');
                res_val = res_val * 2;
            }
            idx -= 1;
        }
    }

    return res;
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
    // Compute numeric value of sx
    let len_x = sx.len() as int;
    let mut ix: int = 0;
    let mut a: nat = 0;
    while ix < len_x
        invariant
            a == Str2Int(sx@.subrange(0, ix)),
        decreases len_x - ix
    {
        if sx@.index(ix) == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        ix += 1;
    }

    // Compute numeric value of sy
    let len_y = sy.len() as int;
    let mut iy: int = 0;
    let mut e: nat = 0;
    while iy < len_y
        invariant
            e == Str2Int(sy@.subrange(0, iy)),
        decreases len_y - iy
    {
        if sy@.index(iy) == '1' {
            e = 2 * e + 1;
        } else {
            e = 2 * e;
        }
        iy += 1;
    }

    // Compute modulus value
    let len_z = sz.len() as int;
    let mut iz: int = 0;
    let mut m: nat = 0;
    while iz < len_z
        invariant
            m == Str2Int(sz@.subrange(0, iz)),
        decreases len_z - iz
    {
        if sz@.index(iz) == '1' {
            m = 2 * m + 1;
        } else {
            m = 2 * m;
        }
        iz += 1;
    }

    // Compute result value
    let mut res_val: nat;
    if e == 0 {
        // x^0 mod m
        res_val = 1 % m;
    } else {
        // e == 2^n by precondition: compute x^(2^n) by n repeated squarings
        res_val = a % m;
        let mut cnt: int = 0;
        while cnt < n
            invariant
                res_val < m,
            decreases n - cnt
        {
            res_val = (res_val * res_val) % m;
            cnt += 1;
        }
    }

    // Convert res_val to Vec<char>
    let mut res: Vec<char> = Vec::new();
    if res_val != 0 {
        let mut pow: nat = 1;
        let mut k: int = 0;
        while pow * 2 <= res_val
            invariant
                pow == Exp_int(2, k as nat),
            decreases res_val - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut idx: int = k;
        let mut acc: nat = 0;
        let mut rem: nat = res_val;
        while idx >= 0
            invariant
                acc == Str2Int(res@),
                rem + acc * Exp_int(2, (idx as nat) + 1) == res_val,
            decreases idx + 1
        {
            let powi = Exp_int(2, idx as nat);
            if rem >= powi {
                res.push('1');
                acc = acc * 2 + 1;
                rem = rem - powi;
            } else {
                res.push('0');
                acc = acc * 2;
            }
            idx -= 1;
        }
    }

    return res;
}

// </vc-code>

fn main() {}
}
