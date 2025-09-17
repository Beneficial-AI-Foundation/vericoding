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
    /* code modified by LLM (iteration 7): addition via Str2Int then reconstruct binary */
    let sum: nat = Str2Int(s1@) + Str2Int(s2@);
    if sum == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = sum;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            0usize <= k && k <= rlen,
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
    /* code modified by LLM (iteration 7): multiplication via Str2Int then reconstruct binary */
    let prod: nat = Str2Int(s1@) * Str2Int(s2@);
    if prod == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = prod;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            0usize <= k && k <= rlen,
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
    /* code modified by LLM (iteration 7): modular exponentiation for exponent 0 or 2^n using nat arithmetic and reconstruction */
    let modulo: nat = Str2Int(sz@);

    // modulo > 1 guaranteed by requires, but handle zero case defensively
    if modulo == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let base: nat = Str2Int(sx@) % modulo;
    let result_nat: nat;

    if Str2Int(sy@) == 0 {
        result_nat = 1 % modulo;
    } else {
        // sy@ == 2^n by precondition, perform n squarings
        let mut i: int = 0;
        let mut cur: nat = base;
        while i < n
            invariant
                0 <= i && i <= n,
            decreases n - i
        {
            cur = (cur * cur) % modulo;
            i += 1;
        }
        result_nat = cur;
    }

    if result_nat == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = result_nat;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            0usize <= k && k <= rlen,
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
