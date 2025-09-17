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
    /* code modified by LLM (iteration 4): use tracked ghost nat variables instead of plain nat to avoid ghost-type errors */
    let mut tracked v1: nat = 0 as nat;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            v1 == Str2Int(s1@.subrange(0, i as int)),
        decreases (s1.len() - i) as nat
    {
        let tracked bit: nat = if s1[i] == '1' { 1 as nat } else { 0 as nat };
        v1 = (2 as nat) * v1 + bit;
        i += 1;
    }

    let mut tracked v2: nat = 0 as nat;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            j <= s2.len(),
            v2 == Str2Int(s2@.subrange(0, j as int)),
        decreases (s2.len() - j) as nat
    {
        let tracked bit: nat = if s2[j] == '1' { 1 as nat } else { 0 as nat };
        v2 = (2 as nat) * v2 + bit;
        j += 1;
    }

    let tracked sum: nat = v1 + v2;
    if sum == 0 as nat {
        return Vec::<char>::new();
    }

    let mut tracked power: nat = 1 as nat;
    while (power * (2 as nat)) <= sum
        invariant
            power >= 1 as nat,
            power <= sum,
        decreases sum - power
    {
        power = power * (2 as nat);
    }

    let mut tracked rem: nat = sum;
    let mut res: Vec<char> = Vec::new();
    let mut tracked p: nat = power;
    while p > 1 as nat
        invariant
            rem < (2 as nat) * p,
            rem + Str2Int(res@) * (2 as nat) * p == sum,
        decreases p
    {
        if rem >= p {
            res.push('1');
            rem = rem - p;
        } else {
            res.push('0');
        }
        p = p / (2 as nat);
    }

    if rem >= 1 as nat {
        res.push('1');
        rem = rem - 1 as nat;
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
    /* code modified by LLM (iteration 4): use tracked nat ghost variables and inline nat->Vec<char> conversion to avoid nested nat functions */
    // convert dividend to nat (tracked)
    let mut tracked n: nat = 0 as nat;
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            n == Str2Int(dividend@.subrange(0, i as int)),
        decreases (dividend.len() - i) as nat
    {
        let tracked bit: nat = if dividend[i] == '1' { 1 as nat } else { 0 as nat };
        n = (2 as nat) * n + bit;
        i += 1;
    }
    // convert divisor to nat (tracked)
    let mut tracked d: nat = 0 as nat;
    let mut j: usize = 0;
    while j < divisor.len()
        invariant
            j <= divisor.len(),
            d == Str2Int(divisor@.subrange(0, j as int)),
        decreases (divisor.len() - j) as nat
    {
        let tracked bit: nat = if divisor[j] == '1' { 1 as nat } else { 0 as nat };
        d = (2 as nat) * d + bit;
        j += 1;
    }

    // compute quotient and remainder using native tracked division
    let tracked q: nat = n / d;
    let tracked r: nat = n % d;

    // convert tracked q -> Vec<char>
    let qv = {
        if q == 0 as nat {
            Vec::<char>::new()
        } else {
            let mut tracked value: nat = q;
            let mut tracked power: nat = 1 as nat;
            while (power * (2 as nat)) <= value
                invariant
                    power >= 1 as nat,
                    power <= value,
                decreases value - power
            {
                power = power * (2 as nat);
            }
            let mut tracked rem2: nat = value;
            let mut out: Vec<char> = Vec::new();
            let mut tracked p2: nat = power;
            while p2 > 1 as nat
                invariant
                    rem2 < (2 as nat) * p2,
                    rem2 + Str2Int(out@) * (2 as nat) * p2 == value,
                decreases p2
            {
                if rem2 >= p2 {
                    out.push('1');
                    rem2 = rem2 - p2;
                } else {
                    out.push('0');
                }
                p2 = p2 / (2 as nat);
            }
            if rem2 >= 1 as nat {
                out.push('1');
                rem2 = rem2 - 1 as nat;
            } else {
                out.push('0');
            }
            out
        }
    };

    // convert tracked r -> Vec<char>
    let rv = {
        if r == 0 as nat {
            Vec::<char>::new()
        } else {
            let mut tracked value: nat = r;
            let mut tracked power: nat = 1 as nat;
            while (power * (2 as nat)) <= value
                invariant
                    power >= 1 as nat,
                    power <= value,
                decreases value - power
            {
                power = power * (2 as nat);
            }
            let mut tracked rem2: nat = value;
            let mut out: Vec<char> = Vec::new();
            let mut tracked p2: nat = power;
            while p2 > 1 as nat
                invariant
                    rem2 < (2 as nat) * p2,
                    rem2 + Str2Int(out@) * (2 as nat) * p2 == value,
                decreases p2
            {
                if rem2 >= p2 {
                    out.push('1');
                    rem2 = rem2 - p2;
                } else {
                    out.push('0');
                }
                p2 = p2 / (2 as nat);
            }
            if rem2 >= 1 as nat {
                out.push('1');
                rem2 = rem2 - 1 as nat;
            } else {
                out.push('0');
            }
            out
        }
    };

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
    /* code modified by LLM (iteration 4): use tracked nat ghost variables for conversions and modular exponentiation to avoid ghost-type errors */
    // convert sx to tracked nat
    let mut tracked base0: nat = 0 as nat;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
            base0 == Str2Int(sx@.subrange(0, i as int)),
        decreases (sx.len() - i) as nat
    {
        let tracked bit: nat = if sx[i] == '1' { 1 as nat } else { 0 as nat };
        base0 = (2 as nat) * base0 + bit;
        i += 1;
    }
    // convert sy to tracked nat
    let mut tracked exp0: nat = 0 as nat;
    let mut j: usize = 0;
    while j < sy.len()
        invariant
            j <= sy.len(),
            exp0 == Str2Int(sy@.subrange(0, j as int)),
        decreases (sy.len() - j) as nat
    {
        let tracked bit: nat = if sy[j] == '1' { 1 as nat } else { 0 as nat };
        exp0 = (2 as nat) * exp0 + bit;
        j += 1;
    }
    // convert sz to tracked nat
    let mut tracked m: nat = 0 as nat;
    let mut k: usize = 0;
    while k < sz.len()
        invariant
            k <= sz.len(),
            m == Str2Int(sz@.subrange(0, k as int)),
        decreases (sz.len() - k) as nat
    {
        let tracked bit: nat = if sz[k] == '1' { 1 as nat } else { 0 as nat };
        m = (2 as nat) * m + bit;
        k += 1;
    }

    // fast exponentiation using tracked nat variables
    let mut tracked pow: nat = 1 as nat;
    let mut tracked b: nat = base0;
    let mut tracked e: nat = exp0;
    while e > 0 as nat
        invariant
            pow * Exp_int(b, e) == Exp_int(base0, exp0),
        decreases e
    {
        if e % (2 as nat) == 1 as nat {
            pow = pow * b;
            e = e - 1 as nat;
        } else {
            b = b * b;
            e = e / (2 as nat);
        }
    }

    let tracked res_nat: nat = pow % m;

    // convert tracked res_nat to Vec<char>
    if res_nat == 0 as nat {
        return Vec::<char>::new();
    }
    let mut tracked power: nat = 1 as nat;
    while (power * (2 as nat)) <= res_nat
        invariant
            power >= 1 as nat,
            power <= res_nat,
        decreases res_nat - power
    {
        power = power * (2 as nat);
    }
    let mut tracked rem2: nat = res_nat;
    let mut out: Vec<char> = Vec::new();
    let mut tracked p2: nat = power;
    while p2 > 1 as nat
        invariant
            rem2 < (2 as nat) * p2,
            rem2 + Str2Int(out@) * (2 as nat) * p2 == res_nat,
        decreases p2
    {
        if rem2 >= p2 {
            out.push('1');
            rem2 = rem2 - p2;
        } else {
            out.push('0');
        }
        p2 = p2 / (2 as nat);
    }
    if rem2 >= 1 as nat {
        out.push('1');
        rem2 = rem2 - 1 as nat;
    } else {
        out.push('0');
    }

    out
}
// </vc-code>

fn main() {}
}


