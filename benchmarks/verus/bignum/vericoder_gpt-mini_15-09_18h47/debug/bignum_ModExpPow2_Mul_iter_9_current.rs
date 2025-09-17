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
    /* code modified by LLM (iteration 9): convert bit strings to nat and multiply, then convert to bit vector */
    let mut a: nat = 0nat;
    let mut idx: usize = 0;
    while idx < s1.len()
        invariant
            idx <= s1.len(),
        decreases s1.len() - idx
    {
        a = a * 2nat + (if s1[idx] == '1' { 1nat } else { 0nat });
        idx += 1;
    }

    let mut b: nat = 0nat;
    idx = 0;
    while idx < s2.len()
        invariant
            idx <= s2.len(),
        decreases s2.len() - idx
    {
        b = b * 2nat + (if s2[idx] == '1' { 1nat } else { 0nat });
        idx += 1;
    }

    let prod: nat = a * b;

    let mut res = Vec::<char>::new();
    if prod == 0nat {
        res.push('0');
        return res;
    }

    let mut bits_rev = Vec::<char>::new();
    let mut v: nat = prod;
    while v > 0nat
        invariant
            v >= 0nat,
        decreases v
    {
        let bit = if v % 2nat == 1nat { '1' } else { '0' };
        bits_rev.push(bit);
        v = v / 2nat;
    }

    let mut p: usize = 0;
    while p < bits_rev.len()
        invariant
            p <= bits_rev.len(),
        decreases bits_rev.len() - p
    {
        res.insert(0, bits_rev[p]);
        p += 1;
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
    /* code modified by LLM (iteration 9): compute base, modulus, and exponent as nat; perform repeated squaring for exponent 2^n, then convert result to bit vector */
    let mut base: nat = 0nat;
    let mut idx: usize = 0;
    while idx < sx.len()
        invariant
            idx <= sx.len(),
        decreases sx.len() - idx
    {
        base = base * 2nat + (if sx[idx] == '1' { 1nat } else { 0nat });
        idx += 1;
    }

    let mut modu: nat = 0nat;
    idx = 0;
    while idx < sz.len()
        invariant
            idx <= sz.len(),
        decreases sz.len() - idx
    {
        modu = modu * 2nat + (if sz[idx] == '1' { 1nat } else { 0nat });
        idx += 1;
    }

    if modu == 0nat {
        let mut r = Vec::<char>::new();
        r.push('0');
        return r;
    }

    let mut exp: nat = 0nat;
    idx = 0;
    while idx < sy.len()
        invariant
            idx <= sy.len(),
        decreases sy.len() - idx
    {
        exp = exp * 2nat + (if sy[idx] == '1' { 1nat } else { 0nat });
        idx += 1;
    }

    let mut result_int: nat;
    if exp == 0nat {
        result_int = 1nat % modu;
    } else {
        // According to spec, sy represents 2^n (or 0). We perform n squarings starting from base % modu.
        result_int = base % modu;
        // number of squarings equals sy.len() - 1 per spec (sy.len() == n + 1)
        let n_usize: usize = if sy.len() == 0 { 0 } else { sy.len() - 1 };
        let mut c: usize = 0;
        while c < n_usize
            invariant
                c <= n_usize,
            decreases n_usize - c
        {
            result_int = (result_int * result_int) % modu;
            c += 1;
        }
    }

    let mut res = Vec::<char>::new();
    if result_int == 0nat {
        res.push('0');
        return res;
    }

    let mut bits_rev = Vec::<char>::new();
    let mut v: nat = result_int;
    while v > 0nat
        invariant
            v >= 0nat,
        decreases v
    {
        let bit = if v % 2nat == 1nat { '1' } else { '0' };
        bits_rev.push(bit);
        v = v / 2nat;
    }

    let mut p: usize = 0;
    while p < bits_rev.len()
        invariant
            p <= bits_rev.len(),
        decreases bits_rev.len() - p
    {
        res.insert(0, bits_rev[p]);
        p += 1;
    }

    res
}
// </vc-code>

fn main() {}
}


