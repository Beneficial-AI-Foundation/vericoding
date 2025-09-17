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
    let mut v1: nat = 0;
    let mut i: int = 0;
    while i < s1.len() as int
        invariant
            0 <= i && i <= s1.len() as int,
            v1 == Str2Int(s1@.subrange(0, i as int)),
        decreases s1.len() as int - i
    {
        let bit = if s1[i as usize] == '1' { 1nat } else { 0nat };
        v1 = 2 * v1 + bit;
        i += 1;
    }

    let mut v2: nat = 0;
    let mut j: int = 0;
    while j < s2.len() as int
        invariant
            0 <= j && j <= s2.len() as int,
            v2 == Str2Int(s2@.subrange(0, j as int)),
        decreases s2.len() as int - j
    {
        let bit = if s2[j as usize] == '1' { 1nat } else { 0nat };
        v2 = 2 * v2 + bit;
        j += 1;
    }

    let mut sum: nat = v1 + v2;
    if sum == 0 {
        return Vec::<char>::new();
    }

    let mut power: nat = 1;
    while power * 2 <= sum
        invariant
            power >= 1,
            power <= sum,
        decreases sum - power
    {
        power = power * 2;
    }

    let mut rem: nat = sum;
    let mut res = Vec::<char>::new();
    let mut p: nat = power;
    while p > 1
        invariant
            rem < 2 * p,
            rem + Str2Int(res@) * 2 * p == sum,
        decreases p
    {
        if rem >= p {
            res.push('1');
            rem = rem - p;
        } else {
            res.push('0');
        }
        p = p / 2;
    }

    if rem >= 1 {
        res.push('1');
        rem = rem - 1;
    } else {
        res.push('0');
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
    // convert dividend to nat
    let mut n: nat = 0;
    let mut i: int = 0;
    while i < dividend.len() as int
        invariant
            0 <= i && i <= dividend.len() as int,
            n == Str2Int(dividend@.subrange(0, i as int)),
        decreases dividend.len() as int - i
    {
        let bit = if dividend[i as usize] == '1' { 1nat } else { 0nat };
        n = 2 * n + bit;
        i += 1;
    }
    // convert divisor to nat
    let mut d: nat = 0;
    let mut j: int = 0;
    while j < divisor.len() as int
        invariant
            0 <= j && j <= divisor.len() as int,
            d == Str2Int(divisor@.subrange(0, j as int)),
        decreases divisor.len() as int - j
    {
        let bit = if divisor[j as usize] == '1' { 1nat } else { 0nat };
        d = 2 * d + bit;
        j += 1;
    }

    // compute quotient and remainder using native division
    let q: nat = n / d;
    let r: nat = n % d;

    // helper: convert nat -> Vec<char>
    fn __nat_to_vec(mut value: nat) -> Vec<char> {
        if value == 0 {
            return Vec::<char>::new();
        }
        let mut power: nat = 1;
        while power * 2 <= value
            invariant
                power >= 1,
                power <= value,
            decreases value - power
        {
            power = power * 2;
        }
        let mut rem2: nat = value;
        let mut out = Vec::<char>::new();
        let mut p2: nat = power;
        while p2 > 1
            invariant
                rem2 < 2 * p2,
                rem2 + Str2Int(out@) * 2 * p2 == value,
            decreases p2
        {
            if rem2 >= p2 {
                out.push('1');
                rem2 = rem2 - p2;
            } else {
                out.push('0');
            }
            p2 = p2 / 2;
        }
        if rem2 >= 1 {
            out.push('1');
            rem2 = rem2 - 1;
        } else {
            out.push('0');
        }
        out
    }

    let qv = __nat_to_vec(q);
    let rv = __nat_to_vec(r);
    (qv, rv)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // convert sx, sy, sz to nats
    let mut base0: nat = 0;
    let mut i: int = 0;
    while i < sx.len() as int
        invariant
            0 <= i && i <= sx.len() as int,
            base0 == Str2Int(sx@.subrange(0, i as int)),
        decreases sx.len() as int - i
    {
        let bit = if sx[i as usize] == '1' { 1nat } else { 0nat };
        base0 = 2 * base0 + bit;
        i += 1;
    }
    let mut exp0: nat = 0;
    let mut j: int = 0;
    while j < sy.len() as int
        invariant
            0 <= j && j <= sy.len() as int,
            exp0 == Str2Int(sy@.subrange(0, j as int)),
        decreases sy.len() as int - j
    {
        let bit = if sy[j as usize] == '1' { 1nat } else { 0nat };
        exp0 = 2 * exp0 + bit;
        j += 1;
    }
    let mut m: nat = 0;
    let mut k: int = 0;
    while k < sz.len() as int
        invariant
            0 <= k && k <= sz.len() as int,
            m == Str2Int(sz@.subrange(0, k as int)),
        decreases sz.len() as int - k
    {
        let bit = if sz[k as usize] == '1' { 1nat } else { 0nat };
        m = 2 * m + bit;
        k += 1;
    }

    // compute pow = Exp_int(base0, exp0) via fast exponentiation (exact, no mod)
    let mut pow: nat = 1;
    let mut b: nat = base0;
    let mut e: nat = exp0;
    while e > 0
        invariant
            pow * Exp_int(b, e) == Exp_int(base0, exp0),
        decreases e
    {
        if e % 2 == 1 {
            pow = pow * b;
            e = e - 1;
        } else {
            b = b * b;
            e = e / 2;
        }
    }

    let res_nat: nat = pow % m;

    // convert res_nat to Vec<char>
    if res_nat == 0 {
        return Vec::<char>::new();
    }
    let mut power: nat = 1;
    while power * 2 <= res_nat
        invariant
            power >= 1,
            power <= res_nat,
        decreases res_nat - power
    {
        power = power * 2;
    }
    let mut rem2: nat = res_nat;
    let mut out = Vec::<char>::new();
    let mut p2: nat = power;
    while p2 > 1
        invariant
            rem2 < 2 * p2,
            rem2 + Str2Int(out@) * 2 * p2 == res_nat,
        decreases p2
    {
        if rem2 >= p2 {
            out.push('1');
            rem2 = rem2 - p2;
        } else {
            out.push('0');
        }
        p2 = p2 / 2;
    }
    if rem2 >= 1 {
        out.push('1');
        rem2 = rem2 - 1;
    } else {
        out.push('0');
    }

    out
}
// </vc-code>

fn main() {}
}


