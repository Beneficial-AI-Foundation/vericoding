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
    /* code modified by LLM (iteration 10): compute integers from bit strings then add and reconstruct binary */
    let mut v1: usize = 0usize;
    let mut i: usize = 0usize;
    while i < s1.len()
        invariant
            0usize <= i, i <= s1.len(),
        decreases s1.len() - i
    {
        let bit = if s1[i] == '1' { 1usize } else { 0usize };
        v1 = v1 * 2usize + bit;
        i = i + 1usize;
    }

    let mut v2: usize = 0usize;
    let mut j: usize = 0usize;
    while j < s2.len()
        invariant
            0usize <= j, j <= s2.len(),
        decreases s2.len() - j
    {
        let bit = if s2[j] == '1' { 1usize } else { 0usize };
        v2 = v2 * 2usize + bit;
        j = j + 1usize;
    }

    let sum: usize = v1 + v2;

    if sum == 0usize {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: usize = sum;
    while tmp > 0usize
        invariant
            tmp >= 0usize,
        decreases tmp
    {
        if tmp % 2usize == 1usize { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2usize;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0usize;
    while k < rlen
        invariant
            0usize <= k, k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k = k + 1usize;
    }

    res
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): compute integers from bit strings then multiply and reconstruct binary */
    let mut v1: usize = 0usize;
    let mut i: usize = 0usize;
    while i < s1.len()
        invariant
            0usize <= i, i <= s1.len(),
        decreases s1.len() - i
    {
        let bit = if s1[i] == '1' { 1usize } else { 0usize };
        v1 = v1 * 2usize + bit;
        i = i + 1usize;
    }

    let mut v2: usize = 0usize;
    let mut j: usize = 0usize;
    while j < s2.len()
        invariant
            0usize <= j, j <= s2.len(),
        decreases s2.len() - j
    {
        let bit = if s2[j] == '1' { 1usize } else { 0usize };
        v2 = v2 * 2usize + bit;
        j = j + 1usize;
    }

    let prod: usize = v1 * v2;

    if prod == 0usize {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: usize = prod;
    while tmp > 0usize
        invariant
            tmp >= 0usize,
        decreases tmp
    {
        if tmp % 2usize == 1usize { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2usize;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0usize;
    while k < rlen
        invariant
            0usize <= k, k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k = k + 1usize;
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
    /* code modified by LLM (iteration 10): modular exponentiation for exponents 0 or 2^n using runtime arithmetic and int loop for n */
    // compute modulus as runtime usize
    let mut modulo: usize = 0usize;
    let mut iz: usize = 0usize;
    while iz < sz.len()
        invariant
            0usize <= iz, iz <= sz.len(),
        decreases sz.len() - iz
    {
        let bit = if sz[iz] == '1' { 1usize } else { 0usize };
        modulo = modulo * 2usize + bit;
        iz = iz + 1usize;
    }

    if modulo == 0usize {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    // compute base as runtime usize
    let mut base: usize = 0usize;
    let mut ib: usize = 0usize;
    while ib < sx.len()
        invariant
            0usize <= ib, ib <= sx.len(),
        decreases sx.len() - ib
    {
        let bit = if sx[ib] == '1' { 1usize } else { 0usize };
        base = base * 2usize + bit;
        ib = ib + 1usize;
    }
    base = base % modulo;

    // compute exponent value at runtime to check for zero case
    let mut expv: usize = 0usize;
    let mut ie: usize = 0usize;
    while ie < sy.len()
        invariant
            0usize <= ie, ie <= sy.len(),
        decreases sy.len() - ie
    {
        let bit = if sy[ie] == '1' { 1usize } else { 0usize };
        expv = expv * 2usize + bit;
        ie = ie + 1usize;
    }

    let mut result_nat: usize;
    if expv == 0usize {
        result_nat = 1usize % modulo;
    } else {
        let nn_int: int = n;
        let mut i: int = 0;
        let mut cur: usize = base;
        while i < nn_int
            invariant
                0 <= i, i <= nn_int,
            decreases nn_int - i
        {
            cur = (cur * cur) % modulo;
            i = i + 1;
        }
        result_nat = cur;
    }

    if result_nat == 0usize {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: usize = result_nat;
    while tmp > 0usize
        invariant
            tmp >= 0usize,
        decreases tmp
    {
        if tmp % 2usize == 1usize { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2usize;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0usize;
    while k < rlen
        invariant
            0usize <= k, k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k = k + 1usize;
    }

    res
}
// </vc-code>

fn main() {}
}
