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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<char>::new();
    res.push('0');

    let mut i: usize = 0;
    while i < s2.len()
        invariant
            (i as int) <= (s2.len() as int),
        decreases (s2.len() as int) - (i as int)
    {
        let bit = s2[s2.len() - 1 - i];
        if bit == '1' {
            let mut temp = Vec::<char>::new();
            let mut k: usize = 0;
            while k < i
                invariant
                    (k as int) <= (i as int),
                decreases (i as int) - (k as int)
            {
                temp.push('0');
                k += 1;
            }

            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    (j as int) <= (s1.len() as int),
                decreases (s1.len() as int) - (j as int)
            {
                temp.push(s1[j]);
                j += 1;
            }

            // add res and temp (binary addition)
            let mut sum = Vec::<char>::new();
            let mut carry = false;
            let mut pos: usize = 0;
            let max_len = if res.len() > temp.len() { res.len() } else { temp.len() };
            while pos < max_len
                invariant
                    (pos as int) <= (max_len as int),
                decreases (max_len as int) - (pos as int)
            {
                let ai = if pos < res.len() { res[res.len() - 1 - pos] } else { '0' };
                let bi = if pos < temp.len() { temp[temp.len() - 1 - pos] } else { '0' };
                let mut s_int = 0;
                if ai == '1' { s_int += 1; }
                if bi == '1' { s_int += 1; }
                if carry { s_int += 1; }
                let digit = if s_int % 2 == 1 { '1' } else { '0' };
                carry = s_int >= 2;
                sum.insert(0, digit);
                pos += 1;
            }
            if carry {
                sum.insert(0, '1');
            }
            while sum.len() > 1 && sum[0] == '0'
                invariant
                    (sum.len() as int) >= 0,
                decreases (sum.len() as int)
            {
                sum.remove(0);
            }
            res = sum;
        }
        i += 1;
    }

    if res.len() == 0 {
        res.push('0');
    }

    res
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
    let mut base: int = 0;
    let mut idx: usize = 0;
    while idx < sx.len()
        invariant
            (idx as int) <= (sx.len() as int),
        decreases (sx.len() as int) - (idx as int)
    {
        base = base * 2 + if sx[idx] == '1' { 1 } else { 0 };
        idx += 1;
    }

    // parse sy into exp
    let mut exp: int = 0;
    idx = 0;
    while idx < sy.len()
        invariant
            (idx as int) <= (sy.len() as int),
        decreases (sy.len() as int) - (idx as int)
    {
        exp = exp * 2 + if sy[idx] == '1' { 1 } else { 0 };
        idx += 1;
    }

    // parse sz into modu
    let mut modu: int = 0;
    idx = 0;
    while idx < sz.len()
        invariant
            (idx as int) <= (sz.len() as int),
        decreases (sz.len() as int) - (idx as int)
    {
        modu = modu * 2 + if sz[idx] == '1' { 1 } else { 0 };
        idx += 1;
    }

    // compute result
    let mut result_int: int;
    if exp == 0 {
        result_int = 1 % modu;
    } else {
        let n: int = (sy.len() as int) - 1;
        result_int = base % modu;
        let mut c: int = 0;
        while c < n
            invariant
                c >= 0, c <= n,
            decreases n - c
        {
            result_int = (result_int * result_int) % modu;
            c += 1;
        }
    }

    // convert result_int to bit vector (MSB..LSB, last char is LSB)
    let mut res = Vec::<char>::new();
    if result_int == 0 {
        res.push('0');
        return res;
    }

    let mut bits_rev = Vec::<char>::new();
    let mut v: int = result_int;
    while v > 0
        invariant
            v >= 0,
        decreases v
    {
        let bit = if v % 2 == 1 { '1' } else { '0' };
        bits_rev.push(bit);
        v = v / 2;
    }

    let mut p: usize = 0;
    while p < bits_rev.len()
        invariant
            (p as int) <= (bits_rev.len() as int),
        decreases (bits_rev.len() as int) - (p as int)
    {
        // insert at front to obtain MSB..LSB ordering
        res.insert(0, bits_rev[p]);
        p += 1;
    }

    res
}
// </vc-code>

fn main() {}
}


