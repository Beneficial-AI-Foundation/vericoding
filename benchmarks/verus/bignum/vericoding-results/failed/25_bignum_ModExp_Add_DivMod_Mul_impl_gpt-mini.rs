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
    /* code modified by LLM (iteration 10): convert inputs to nat, add, convert to bits */
    let mut a: nat = 0nat;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            a == Str2Int(s1@.subrange(0, i as int)),
        decreases s1.len() - i
    {
        let c = s1[i];
        a = a * 2nat + (if c == '1' { 1nat } else { 0nat });
        i += 1;
    }

    let mut b: nat = 0nat;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            j <= s2.len(),
            b == Str2Int(s2@.subrange(0, j as int)),
        decreases s2.len() - j
    {
        let c = s2[j];
        b = b * 2nat + (if c == '1' { 1nat } else { 0nat });
        j += 1;
    }

    let sum: nat = a + b;

    let mut tmp: Vec<char> = Vec::<char>::new();
    let mut rem: nat = sum;
    if rem != 0nat {
        while rem > 0nat
            invariant
                rem >= 0nat,
            decreases rem
        {
            tmp.push(if rem % 2nat == 1nat { '1' } else { '0' });
            rem = rem / 2nat;
        }
    }

    let mut res: Vec<char> = Vec::<char>::new();
    let mut k: usize = tmp.len();
    while k > 0
        invariant
            k <= tmp.len(),
        decreases k
    {
        k -= 1;
        res.push(tmp[k]);
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
    /* code modified by LLM (iteration 10): convert dividend/divisor to nat, compute quotient/remainder, convert back to bits */
    let mut dv: nat = 0nat;
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            dv == Str2Int(dividend@.subrange(0, i as int)),
        decreases dividend.len() - i
    {
        let c = dividend[i];
        dv = dv * 2nat + (if c == '1' { 1nat } else { 0nat });
        i += 1;
    }

    let mut ds: nat = 0nat;
    let mut j: usize = 0;
    while j < divisor.len()
        invariant
            j <= divisor.len(),
            ds == Str2Int(divisor@.subrange(0, j as int)),
        decreases divisor.len() - j
    {
        let c = divisor[j];
        ds = ds * 2nat + (if c == '1' { 1nat } else { 0nat });
        j += 1;
    }

    let q: nat = dv / ds;
    let r: nat = dv % ds;

    let mut qtmp: Vec<char> = Vec::<char>::new();
    let mut qrem: nat = q;
    if qrem != 0nat {
        while qrem > 0nat
            invariant
                qrem >= 0nat,
            decreases qrem
        {
            qtmp.push(if qrem % 2nat == 1nat { '1' } else { '0' });
            qrem = qrem / 2nat;
        }
    }
    let mut qres: Vec<char> = Vec::<char>::new();
    let mut qi: usize = qtmp.len();
    while qi > 0
        invariant
            qi <= qtmp.len(),
        decreases qi
    {
        qi -= 1;
        qres.push(qtmp[qi]);
    }

    let mut rtmp: Vec<char> = Vec::<char>::new();
    let mut rrem: nat = r;
    if rrem != 0nat {
        while rrem > 0nat
            invariant
                rrem >= 0nat,
            decreases rrem
        {
            rtmp.push(if rrem % 2nat == 1nat { '1' } else { '0' });
            rrem = rrem / 2nat;
        }
    }
    let mut rres: Vec<char> = Vec::<char>::new();
    let mut ri: usize = rtmp.len();
    while ri > 0
        invariant
            ri <= rtmp.len(),
        decreases ri
    {
        ri -= 1;
        rres.push(rtmp[ri]);
    }

    (qres, rres)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): convert inputs to nat, multiply, convert product to bits */
    let mut a: nat = 0nat;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            a == Str2Int(s1@.subrange(0, i as int)),
        decreases s1.len() - i
    {
        let c = s1[i];
        a = a * 2nat + (if c == '1' { 1nat } else { 0nat });
        i += 1;
    }

    let mut b: nat = 0nat;
    let mut j: usize = 0;
    while j < s2.len()
        invariant
            j <= s2.len(),
            b == Str2Int(s2@.subrange(0, j as int)),
        decreases s2.len() - j
    {
        let c = s2[j];
        b = b * 2nat + (if c == '1' { 1nat } else { 0nat });
        j += 1;
    }

    let prod: nat = a * b;

    let mut tmp: Vec<char> = Vec::<char>::new();
    let mut rem: nat = prod;
    if rem != 0nat {
        while rem > 0nat
            invariant
                rem >= 0nat,
            decreases rem
        {
            tmp.push(if rem % 2nat == 1nat { '1' } else { '0' });
            rem = rem / 2nat;
        }
    }

    let mut res: Vec<char> = Vec::<char>::new();
    let mut k: usize = tmp.len();
    while k > 0
        invariant
            k <= tmp.len(),
        decreases k
    {
        k -= 1;
        res.push(tmp[k]);
    }
    res
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
    /* code modified by LLM (iteration 10): convert inputs to nat, perform modular exponentiation on nat, convert result to bits */
    let mut x: nat = 0nat;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
            x == Str2Int(sx@.subrange(0, i as int)),
        decreases sx.len() - i
    {
        let c = sx[i];
        x = x * 2nat + (if c == '1' { 1nat } else { 0nat });
        i += 1;
    }

    let mut y: nat = 0nat;
    let mut j: usize = 0;
    while j < sy.len()
        invariant
            j <= sy.len(),
            y == Str2Int(sy@.subrange(0, j as int)),
        decreases sy.len() - j
    {
        let c = sy[j];
        y = y * 2nat + (if c == '1' { 1nat } else { 0nat });
        j += 1;
    }

    let mut m: nat = 0nat;
    let mut k: usize = 0;
    while k < sz.len()
        invariant
            k <= sz.len(),
            m == Str2Int(sz@.subrange(0, k as int)),
        decreases sz.len() - k
    {
        let c = sz[k];
        m = m * 2nat + (if c == '1' { 1nat } else { 0nat });
        k += 1;
    }

    let mut result: nat = 1nat % m;
    let mut base: nat = x % m;
    let mut exp: nat = y;
    while exp > 0nat
        invariant
            exp >= 0nat,
        decreases exp
    {
        if exp % 2nat == 1nat {
            result = (result * base) % m;
        }
        base = (base * base) % m;
        exp = exp / 2nat;
    }

    let mut tmp: Vec<char> = Vec::<char>::new();
    let mut rem: nat = result;
    if rem != 0nat {
        while rem > 0nat
            invariant
                rem >= 0nat,
            decreases rem
        {
            tmp.push(if rem % 2nat == 1nat { '1' } else { '0' });
            rem = rem / 2nat;
        }
    }

    let mut res: Vec<char> = Vec::<char>::new();
    let mut t: usize = tmp.len();
    while t > 0
        invariant
            t <= tmp.len(),
        decreases t
    {
        t -= 1;
        res.push(tmp[t]);
    }
    res
}
// </vc-code>

fn main() {}
}
