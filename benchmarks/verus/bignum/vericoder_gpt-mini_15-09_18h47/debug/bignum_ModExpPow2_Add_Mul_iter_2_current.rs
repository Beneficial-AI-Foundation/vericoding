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
    /* code modified by LLM (iteration 2): use usize/u128 for runtime arithmetic and avoid nat/int casts */
    let n1 = s1.len();
    let n2 = s2.len();

    let mut v1: u128 = 0;
    let mut i1: usize = 0;
    while i1 < n1
        invariant
            i1 <= n1,
        decreases n1 - i1
    {
        if s1[i1] == '1' { v1 = v1 * 2 + 1; } else { v1 = v1 * 2; }
        i1 += 1;
    }

    let mut v2: u128 = 0;
    let mut i2: usize = 0;
    while i2 < n2
        invariant
            i2 <= n2,
        decreases n2 - i2
    {
        if s2[i2] == '1' { v2 = v2 * 2 + 1; } else { v2 = v2 * 2; }
        i2 += 1;
    }

    let sum: u128 = v1 + v2;
    if sum == 0 {
        return Vec::<char>::new();
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: u128 = sum;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 {
            rev.push('1');
        } else {
            rev.push('0');
        }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k += 1;
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
    /* code modified by LLM (iteration 2): use usize/u128 for runtime arithmetic and avoid nat/int casts */
    let n1 = s1.len();
    let n2 = s2.len();

    let mut v1: u128 = 0;
    let mut i1: usize = 0;
    while i1 < n1
        invariant
            i1 <= n1,
        decreases n1 - i1
    {
        if s1[i1] == '1' { v1 = v1 * 2 + 1; } else { v1 = v1 * 2; }
        i1 += 1;
    }

    let mut v2: u128 = 0;
    let mut i2: usize = 0;
    while i2 < n2
        invariant
            i2 <= n2,
        decreases n2 - i2
    {
        if s2[i2] == '1' { v2 = v2 * 2 + 1; } else { v2 = v2 * 2; }
        i2 += 1;
    }

    let prod: u128 = v1 * v2;
    if prod == 0 {
        return Vec::<char>::new();
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: u128 = prod;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 {
            rev.push('1');
        } else {
            rev.push('0');
        }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k += 1;
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
    /* code modified by LLM (iteration 2): avoid int/nat by using usize/u128 and derive exponent iterations from sy.len() */
    let n_x = sx.len();
    let mut base: u128 = 0;
    let mut ix: usize = 0;
    while ix < n_x
        invariant
            ix <= n_x,
        decreases n_x - ix
    {
        if sx[ix] == '1' { base = base * 2 + 1; } else { base = base * 2; }
        ix += 1;
    }

    let n_z = sz.len();
    let mut modulo: u128 = 0;
    let mut iz: usize = 0;
    while iz < n_z
        invariant
            iz <= n_z,
        decreases n_z - iz
    {
        if sz[iz] == '1' { modulo = modulo * 2 + 1; } else { modulo = modulo * 2; }
        iz += 1;
    }

    // determine whether exponent (sy) is zero by checking bits at runtime
    let mut sy_has_one: bool = false;
    let mut isy: usize = 0;
    while isy < sy.len()
        invariant
            isy <= sy.len(),
        decreases sy.len() - isy
    {
        if sy[isy] == '1' { sy_has_one = true; }
        isy += 1;
    }
    let exponent_is_zero = !sy_has_one;

    let mut result_val: u128;
    if exponent_is_zero {
        result_val = 1 % modulo;
    } else {
        // per spec sy.len() == n + 1, so number of squarings is sy.len() - 1
        let n_iter = sy.len().saturating_sub(1);
        let mut cur: u128 = base % modulo;
        let mut i: usize = 0;
        while i < n_iter
            invariant
                i <= n_iter,
            decreases n_iter - i
        {
            cur = (cur * cur) % modulo;
            i += 1;
        }
        result_val = cur;
    }

    if result_val == 0 {
        return Vec::<char>::new();
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: u128 = result_val;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 {
            rev.push('1');
        } else {
            rev.push('0');
        }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k += 1;
    }

    res
}
// </vc-code>

fn main() {}
}
