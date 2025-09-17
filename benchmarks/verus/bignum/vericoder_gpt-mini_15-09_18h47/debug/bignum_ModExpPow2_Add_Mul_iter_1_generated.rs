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
    let n1 = s1.len() as int;
    let n2 = s2.len() as int;

    let mut v1: nat = 0;
    let mut i1: int = 0;
    while i1 < n1
        invariant
            0 <= i1 && i1 <= n1,
        decreases n1 - i1
    {
        if s1[i1 as usize] == '1' { v1 = v1 * 2 + 1; } else { v1 = v1 * 2; }
        i1 += 1;
    }

    let mut v2: nat = 0;
    let mut i2: int = 0;
    while i2 < n2
        invariant
            0 <= i2 && i2 <= n2,
        decreases n2 - i2
    {
        if s2[i2 as usize] == '1' { v2 = v2 * 2 + 1; } else { v2 = v2 * 2; }
        i2 += 1;
    }

    let mut sum: nat = v1 + v2;
    if sum == 0 {
        return Vec::<char>::new();
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = sum;
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
    let rlen = rev.len() as int;
    let mut k: int = 0;
    while k < rlen
        invariant
            0 <= k && k <= rlen,
        decreases rlen - k
    {
        res.push(rev[(rlen - 1 - k) as usize]);
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
    let n1 = s1.len() as int;
    let n2 = s2.len() as int;

    let mut v1: nat = 0;
    let mut i1: int = 0;
    while i1 < n1
        invariant
            0 <= i1 && i1 <= n1,
        decreases n1 - i1
    {
        if s1[i1 as usize] == '1' { v1 = v1 * 2 + 1; } else { v1 = v1 * 2; }
        i1 += 1;
    }

    let mut v2: nat = 0;
    let mut i2: int = 0;
    while i2 < n2
        invariant
            0 <= i2 && i2 <= n2,
        decreases n2 - i2
    {
        if s2[i2 as usize] == '1' { v2 = v2 * 2 + 1; } else { v2 = v2 * 2; }
        i2 += 1;
    }

    let mut prod: nat = v1 * v2;
    if prod == 0 {
        return Vec::<char>::new();
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = prod;
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
    let rlen = rev.len() as int;
    let mut k: int = 0;
    while k < rlen
        invariant
            0 <= k && k <= rlen,
        decreases rlen - k
    {
        res.push(rev[(rlen - 1 - k) as usize]);
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
    // compute base = Str2Int(sx@)
    let n_x = sx.len() as int;
    let mut base: nat = 0;
    let mut ix: int = 0;
    while ix < n_x
        invariant
            0 <= ix && ix <= n_x,
        decreases n_x - ix
    {
        if sx[ix as usize] == '1' { base = base * 2 + 1; } else { base = base * 2; }
        ix += 1;
    }

    // compute mod = Str2Int(sz@)
    let n_z = sz.len() as int;
    let mut modulo: nat = 0;
    let mut iz: int = 0;
    while iz < n_z
        invariant
            0 <= iz && iz <= n_z,
        decreases n_z - iz
    {
        if sz[iz as usize] == '1' { modulo = modulo * 2 + 1; } else { modulo = modulo * 2; }
        iz += 1;
    }

    // modulo > 1 by precondition
    let mut result_val: nat;
    if Str2Int(sy@) == 0 {
        // x^0 == 1
        result_val = 1 % modulo;
    } else {
        // exponent is 2^n, compute by n repeated squaring
        let mut cur: nat = base % modulo;
        let mut i: int = 0;
        while i < n
            invariant
                0 <= i && i <= n,
            decreases n - i
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
    let mut tmp: nat = result_val;
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
    let rlen = rev.len() as int;
    let mut k: int = 0;
    while k < rlen
        invariant
            0 <= k && k <= rlen,
        decreases rlen - k
    {
        res.push(rev[(rlen - 1 - k) as usize]);
        k += 1;
    }

    res
}
// </vc-code>

fn main() {}
}
