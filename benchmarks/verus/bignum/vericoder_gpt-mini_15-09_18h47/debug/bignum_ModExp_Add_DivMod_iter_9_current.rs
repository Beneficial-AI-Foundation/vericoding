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
    /* code modified by LLM (iteration 9): binary addition implemented with explicit casts to `int` for literals used in arithmetic */
    let mut i1: usize = s1.len();
    let mut i2: usize = s2.len();
    let mut res_rev: Vec<char> = Vec::new();
    let mut carry: int = 0 as int;
    while i1 > 0 || i2 > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
        decreases i1 + i2
    {
        let b1: int = if i1 > 0 && s1[i1 - 1] == '1' { 1 as int } else { 0 as int };
        let b2: int = if i2 > 0 && s2[i2 - 1] == '1' { 1 as int } else { 0 as int };
        let sum: int = b1 + b2 + carry;
        let bit: char = if sum % (2 as int) == (1 as int) { '1' } else { '0' };
        res_rev.push(bit);
        carry = if sum >= (2 as int) { 1 as int } else { 0 as int };
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }
    if carry == (1 as int) {
        res_rev.push('1');
    }

    // reverse to MSB-first
    let mut res: Vec<char> = Vec::new();
    let mut idx: usize = res_rev.len();
    while idx > 0
        invariant
            idx <= res_rev.len(),
        decreases idx
    {
        res.push(res_rev[idx - 1]);
        idx -= 1;
    }

    // trim leading zeros
    let mut first_one: usize = 0;
    while first_one < res.len() && res[first_one] == '0'
        invariant
            first_one <= res.len(),
        decreases res.len() - first_one
    {
        first_one += 1;
    }

    if first_one == res.len() {
        Vec::<char>::new()
    } else if first_one == 0 {
        res
    } else {
        let mut out: Vec<char> = Vec::new();
        let mut k: usize = first_one;
        while k < res.len()
            invariant
                k <= res.len(),
            decreases res.len() - k
        {
            out.push(res[k]);
            k += 1;
        }
        out
    }
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
    /* code modified by LLM (iteration 9): long division with explicit casts to `int` for borrow arithmetic */
    // copy inputs to Vec<char>
    let mut dividend_v: Vec<char> = Vec::new();
    let mut ii: usize = 0;
    while ii < dividend.len()
        invariant
            ii <= dividend.len(),
        decreases dividend.len() - ii
    {
        dividend_v.push(dividend[ii]);
        ii += 1;
    }
    let mut divisor_v: Vec<char> = Vec::new();
    let mut jj: usize = 0;
    while jj < divisor.len()
        invariant
            jj <= divisor.len(),
        decreases divisor.len() - jj
    {
        divisor_v.push(divisor[jj]);
        jj += 1;
    }

    // trim divisor once (divisor > 0 by precondition)
    let mut df: usize = 0;
    while df < divisor_v.len() && divisor_v[df] == '0'
        invariant
            df <= divisor_v.len(),
        decreases divisor_v.len() - df
    {
        df += 1;
    }
    let mut divisor_trim: Vec<char> = if df == divisor_v.len() { Vec::new() } else {
        let mut tmp: Vec<char> = Vec::new();
        let mut t: usize = df;
        while t < divisor_v.len()
            invariant
                t <= divisor_v.len(),
            decreases divisor_v.len() - t
        {
            tmp.push(divisor_v[t]);
            t += 1;
        }
        tmp
    };

    // long division
    let mut quotient: Vec<char> = Vec::new();
    let mut rem: Vec<char> = Vec::new();

    let mut idxd: usize = 0;
    while idxd < dividend_v.len()
        invariant
            idxd <= dividend_v.len(),
        decreases dividend_v.len() - idxd
    {
        // append next bit
        if rem.len() == 0 && dividend_v[idxd] == '0' {
            // keep rem empty
        } else {
            rem.push(dividend_v[idxd]);
        }

        if rem.len() == 0 {
            quotient.push('0');
        } else {
            // compute first_one for rem
            let mut rfirst: usize = 0;
            while rfirst < rem.len() && rem[rfirst] == '0'
                invariant
                    rfirst <= rem.len(),
                decreases rem.len() - rfirst
            {
                rfirst += 1;
            }
            if rfirst == rem.len() {
                // rem is zero
                quotient.push('0');
            } else {
                let rem_len: usize = rem.len() - rfirst;
                let div_len: usize = divisor_trim.len();
                let mut ge: bool = false;
                if rem_len > div_len {
                    ge = true;
                } else if rem_len < div_len {
                    ge = false;
                } else {
                    // lexicographic compare
                    let mut k: usize = 0;
                    let mut decided: bool = false;
                    while k < rem_len
                        invariant
                            k <= rem_len,
                            rem_len + rfirst == rem.len(),
                            divisor_trim.len() == div_len,
                        decreases rem_len - k
                    {
                        let ca = rem[rfirst + k];
                        let cb = divisor_trim[k];
                        if ca == '1' && cb == '0' { ge = true; decided = true; break; }
                        if ca == '0' && cb == '1' { ge = false; decided = true; break; }
                        k += 1;
                    }
                    if !decided { ge = true; }
                }

                if ge {
                    quotient.push('1');
                    // subtract divisor_trim from rem
                    // reverse rem and divisor_trim to LSB-first
                    let mut ra: Vec<char> = Vec::new();
                    let mut ia: usize = 0;
                    while ia < rem.len()
                        invariant
                            ia <= rem.len(),
                        decreases rem.len() - ia
                    {
                        ra.push(rem[rem.len() - 1 - ia]);
                        ia += 1;
                    }
                    let mut rb: Vec<char> = Vec::new();
                    let mut ib: usize = 0;
                    while ib < divisor_trim.len()
                        invariant
                            ib <= divisor_trim.len(),
                        decreases divisor_trim.len() - ib
                    {
                        rb.push(divisor_trim[divisor_trim.len() - 1 - ib]);
                        ib += 1;
                    }

                    let mut out_rev: Vec<char> = Vec::new();
                    let mut borrow: int = 0 as int;
                    let mut kk: usize = 0;
                    while kk < ra.len()
                        invariant
                            kk <= ra.len(),
                            ra.len() == rem.len(),
                            rb.len() == divisor_trim.len(),
                        decreases ra.len() - kk
                    {
                        let ba: int = if ra[kk] == '1' { 1 as int } else { 0 as int };
                        let bb: int = if kk < rb.len() && rb[kk] == '1' { 1 as int } else { 0 as int };
                        let mut v: int = ba - bb - borrow;
                        if v < 0 as int { v += 2 as int; borrow = 1 as int; } else { borrow = 0 as int; }
                        out_rev.push(if v == (1 as int) { '1' } else { '0' });
                        kk += 1;
                    }
                    // reverse back
                    let mut out: Vec<char> = Vec::new();
                    let mut t: usize = out_rev.len();
                    while t > 0
                        invariant
                            t <= out_rev.len(),
                        decreases t
                    {
                        out.push(out_rev[t - 1]);
                        t -= 1;
                    }
                    // trim out
                    let mut p: usize = 0;
                    while p < out.len() && out[p] == '0'
                        invariant
                            p <= out.len(),
                        decreases out.len() - p
                    {
                        p += 1;
                    }
                    if p == out.len() {
                        rem = Vec::new();
                    } else {
                        let mut nr: Vec<char> = Vec::new();
                        let mut q: usize = p;
                        while q < out.len()
                            invariant
                                q <= out.len(),
                            decreases out.len() - q
                        {
                            nr.push(out[q]);
                            q += 1;
                        }
                        rem = nr;
                    }
                } else {
                    quotient.push('0');
                }
            }
        }

        idxd += 1;
    }

    // trim quotient
    let mut qfirst: usize = 0;
    while qfirst < quotient.len() && quotient[qfirst] == '0'
        invariant
            qfirst <= quotient.len(),
        decreases quotient.len() - qfirst
    {
        qfirst += 1;
    }
    let q_trim: Vec<char> = if qfirst == quotient.len() { Vec::new() } else {
        let mut qq: Vec<char> = Vec::new();
        let mut u: usize = qfirst;
        while u < quotient.len()
            invariant
                u <= quotient.len(),
            decreases quotient.len() - u
        {
            qq.push(quotient[u]);
            u += 1;
        }
        qq
    };

    // trim remainder
    let mut rfirst2: usize = 0;
    while rfirst2 < rem.len() && rem[rfirst2] == '0'
        invariant
            rfirst2 <= rem.len(),
        decreases rem.len() - rfirst2
    {
        rfirst2 += 1;
    }
    let r_trim: Vec<char> = if rfirst2 == rem.len() { Vec::new() } else {
        let mut rr: Vec<char> = Vec::new();
        let mut v: usize = rfirst2;
        while v < rem.len()
            invariant
                v <= rem.len(),
            decreases rem.len() - v
        {
            rr.push(rem[v]);
            v += 1;
        }
        rr
    };

    (q_trim, r_trim)
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
    /* code modified by LLM (iteration 9): modular exponentiation by squaring using Add and DivMod, no int-literals required here */
    // convert inputs to Vec<char>
    let mut base: Vec<char> = Vec::new();
    let mut xi: usize = 0;
    while xi < sx.len()
        invariant
            xi <= sx.len(),
        decreases sx.len() - xi
    {
        base.push(sx[xi]);
        xi += 1;
    }
    let mut exp: Vec<char> = Vec::new();
    let mut yi: usize = 0;
    while yi < sy.len()
        invariant
            yi <= sy.len(),
        decreases sy.len() - yi
    {
        exp.push(sy[yi]);
        yi += 1;
    }
    let mut modu: Vec<char> = Vec::new();
    let mut zi: usize = 0;
    while zi < sz.len()
        invariant
            zi <= sz.len(),
        decreases sz.len() - zi
    {
        modu.push(sz[zi]);
        zi += 1;
    }

    // initialize result = 1 mod m
    let mut result: Vec<char> = Vec::new();
    result.push('1');
    // ensure result trimmed and reduced
    result = DivMod(result.as_slice(), modu.as_slice()).1;

    // exponentiation by squaring: process bits from LSB to MSB
    let mut k: usize = 0;
    while k < exp.len()
        invariant
            k <= exp.len(),
        decreases exp.len() - k
    {
        let bit = exp[exp.len() - 1 - k];
        if bit == '1' {
            // prod = result * base (inline multiplication)
            let mut prod: Vec<char> = Vec::new();
            let mut i: usize = 0;
            while i < base.len()
                invariant
                    i <= base.len(),
                decreases base.len() - i
            {
                let idx = base.len() - 1 - i;
                if base[idx] == '1' {
                    // shifted = result shifted by i (append i zeros)
                    let mut shifted: Vec<char> = Vec::new();
                    let mut k2: usize = 0;
                    while k2 < result.len()
                        invariant
                            k2 <= result.len(),
                        decreases result.len() - k2
                    {
                        shifted.push(result[k2]);
                        k2 += 1;
                    }
                    let mut z: usize = 0;
                    while z < i
                        invariant
                            z <= i,
                        decreases i - z
                    {
                        shifted.push('0');
                        z += 1;
                    }
                    prod = Add(prod.as_slice(), shifted.as_slice());
                }
                i += 1;
            }
            // reduce modulo
            let r = DivMod(prod.as_slice(), modu.as_slice()).1;
            result = r;
        }

        // base = (base * base) % modu  (inline multiplication)
        let mut b2prod: Vec<char> = Vec::new();
        let mut i2: usize = 0;
        while i2 < base.len()
            invariant
                i2 <= base.len(),
            decreases base.len() - i2
        {
            let idx2 = base.len() - 1 - i2;
            if base[idx2] == '1' {
                let mut shifted2: Vec<char> = Vec::new();
                let mut k3: usize = 0;
                while k3 < base.len()
                    invariant
                        k3 <= base.len(),
                    decreases base.len() - k3
                {
                    shifted2.push(base[k3]);
                    k3 += 1;
                }
                let mut z2: usize = 0;
                while z2 < i2
                    invariant
                        z2 <= i2,
                    decreases i2 - z2
                {
                    shifted2.push('0');
                    z2 += 1;
                }
                b2prod = Add(b2prod.as_slice(), shifted2.as_slice());
            }
            i2 += 1;
        }
        base = DivMod(b2prod.as_slice(), modu.as_slice()).1;

        k += 1;
    }

    // trim result (remove leading zeros)
    let mut rf: usize = 0;
    while rf < result.len() && result[rf] == '0'
        invariant
            rf <= result.len(),
        decreases result.len() - rf
    {
        rf += 1;
    }
    if rf == result.len() {
        Vec::<char>::new()
    } else if rf == 0 {
        result
    } else {
        let mut out: Vec<char> = Vec::new();
        let mut kk: usize = rf;
        while kk < result.len()
            invariant
                kk <= result.len(),
            decreases result.len() - kk
        {
            out.push(result[kk]);
            kk += 1;
        }
        out
    }
}

// </vc-code>

fn main() {}
}


