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
    /* code modified by LLM (iteration 9): compute quotient and remainder by converting bit-strings to runtime integers and back */
    let len_d = dividend.len();
    let mut i: usize = 0;
    let mut a: usize = 0;
    while i < len_d
        invariant
            a == (Str2Int(dividend@.subrange(0, i as int)) as usize),
        decreases len_d - i
    {
        if dividend[i] == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        i += 1;
    }

    let len_v = divisor.len();
    let mut j: usize = 0;
    let mut b: usize = 0;
    while j < len_v
        invariant
            b == (Str2Int(divisor@.subrange(0, j as int)) as usize),
        decreases len_v - j
    {
        if divisor[j] == '1' {
            b = 2 * b + 1;
        } else {
            b = 2 * b;
        }
        j += 1;
    }

    let q: usize = a / b;
    let r: usize = a % b;

    let mut res_q: Vec<char> = Vec::new();
    if q != 0 {
        let mut pow: usize = 1;
        let mut k: usize = 0;
        while pow * 2 <= q
            invariant
                pow <= q && pow == (1usize << k),
            decreases q - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut t: usize = k + 1;
        let mut rem: usize = q;
        let mut res_val: usize = 0;
        while t > 0
            invariant
                res_val == (Str2Int(res_q@) as usize),
            decreases t
        {
            t -= 1;
            let powi: usize = 1usize << t;
            if rem >= powi {
                res_q.push('1');
                res_val = res_val * 2 + 1;
                rem = rem - powi;
            } else {
                res_q.push('0');
                res_val = res_val * 2;
            }
        }
    }

    let mut res_r: Vec<char> = Vec::new();
    if r != 0 {
        let mut pow2: usize = 1;
        let mut k2: usize = 0;
        while pow2 * 2 <= r
            invariant
                pow2 <= r && pow2 == (1usize << k2),
            decreases r - pow2
        {
            pow2 = pow2 * 2;
            k2 += 1;
        }

        let mut tr: usize = k2 + 1;
        let mut rem2: usize = r;
        let mut res_val2: usize = 0;
        while tr > 0
            invariant
                res_val2 == (Str2Int(res_r@) as usize),
            decreases tr
        {
            tr -= 1;
            let powi: usize = 1usize << tr;
            if rem2 >= powi {
                res_r.push('1');
                res_val2 = res_val2 * 2 + 1;
                rem2 = rem2 - powi;
            } else {
                res_r.push('0');
                res_val2 = res_val2 * 2;
            }
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
    /* code modified by LLM (iteration 9): multiply two bit-strings by converting to runtime integers and back */
    let len1 = s1.len();
    let mut i: usize = 0;
    let mut a: usize = 0;
    while i < len1
        invariant
            a == (Str2Int(s1@.subrange(0, i as int)) as usize),
        decreases len1 - i
    {
        if s1[i] == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        i += 1;
    }

    let len2 = s2.len();
    let mut j: usize = 0;
    let mut b: usize = 0;
    while j < len2
        invariant
            b == (Str2Int(s2@.subrange(0, j as int)) as usize),
        decreases len2 - j
    {
        if s2[j] == '1' {
            b = 2 * b + 1;
        } else {
            b = 2 * b;
        }
        j += 1;
    }

    let p: usize = a * b;

    let mut res: Vec<char> = Vec::new();
    if p != 0 {
        let mut pow: usize = 1;
        let mut k: usize = 0;
        while pow * 2 <= p
            invariant
                pow <= p && pow == (1usize << k),
            decreases p - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut t: usize = k + 1;
        let mut rem: usize = p;
        let mut res_val: usize = 0;
        while t > 0
            invariant
                res_val == (Str2Int(res@) as usize),
            decreases t
        {
            t -= 1;
            let powi: usize = 1usize << t;
            if rem >= powi {
                res.push('1');
                res_val = res_val * 2 + 1;
                rem = rem - powi;
            } else {
                res.push('0');
                res_val = res_val * 2;
            }
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
    /* code modified by LLM (iteration 9): compute modular exponentiation using integer loop counter converted to usize */
    let len_x = sx.len();
    let mut ix: usize = 0;
    let mut a: usize = 0;
    while ix < len_x
        invariant
            a == (Str2Int(sx@.subrange(0, ix as int)) as usize),
        decreases len_x - ix
    {
        if sx[ix] == '1' {
            a = 2 * a + 1;
        } else {
            a = 2 * a;
        }
        ix += 1;
    }

    let len_y = sy.len();
    let mut iy: usize = 0;
    let mut _e: usize = 0; // numeric exponent (not used directly since we rely on n)
    while iy < len_y
        invariant
            _e == (Str2Int(sy@.subrange(0, iy as int)) as usize),
        decreases len_y - iy
    {
        if sy[iy] == '1' {
            _e = 2 * _e + 1;
        } else {
            _e = 2 * _e;
        }
        iy += 1;
    }

    let len_z = sz.len();
    let mut iz: usize = 0;
    let mut m: usize = 0;
    while iz < len_z
        invariant
            m == (Str2Int(sz@.subrange(0, iz as int)) as usize),
        decreases len_z - iz
    {
        if sz[iz] == '1' {
            m = 2 * m + 1;
        } else {
            m = 2 * m;
        }
        iz += 1;
    }

    let mut res_val: usize;
    if _e == 0 {
        res_val = 1 % m;
    } else {
        res_val = a % m;
        let nn: usize = n as usize;
        let mut cnt: usize = 0;
        while cnt < nn
            invariant
                res_val < m,
            decreases nn - cnt
        {
            res_val = (res_val * res_val) % m;
            cnt += 1;
        }
    }

    let mut res: Vec<char> = Vec::new();
    if res_val != 0 {
        let mut pow: usize = 1;
        let mut k: usize = 0;
        while pow * 2 <= res_val
            invariant
                pow <= res_val && pow == (1usize << k),
            decreases res_val - pow
        {
            pow = pow * 2;
            k += 1;
        }

        let mut t: usize = k + 1;
        let mut acc: usize = 0;
        let mut rem: usize = res_val;
        while t > 0
            invariant
                acc == (Str2Int(res@) as usize),
            decreases t
        {
            t -= 1;
            let powi: usize = 1usize << t;
            if rem >= powi {
                res.push('1');
                acc = acc * 2 + 1;
                rem = rem - powi;
            } else {
                res.push('0');
                acc = acc * 2;
            }
        }
    }

    return res;
}
// </vc-code>

fn main() {}
}
