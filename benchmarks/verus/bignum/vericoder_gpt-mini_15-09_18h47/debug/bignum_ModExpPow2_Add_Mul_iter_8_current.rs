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
    /* code modified by LLM (iteration 8): addition via nat arithmetic and binary reconstruction */
    let sum: nat = Str2Int(s1@) + Str2Int(s2@);
    if sum == 0nat {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = sum;
    while tmp > 0nat
        invariant
            tmp >= 0nat,
        decreases tmp
    {
        if tmp % 2nat == 1nat { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2nat;
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
    /* code modified by LLM (iteration 8): multiplication via nat arithmetic and binary reconstruction */
    let prod: nat = Str2Int(s1@) * Str2Int(s2@);
    if prod == 0nat {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = prod;
    while tmp > 0nat
        invariant
            tmp >= 0nat,
        decreases tmp
    {
        if tmp % 2nat == 1nat { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2nat;
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
    /* code modified by LLM (iteration 8): modular exponentiation for exponents 0 or 2^n with nat arithmetic */
    let modulo: nat = Str2Int(sz@);

    if modulo == 0nat {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let base: nat = Str2Int(sx@) % modulo;
    let result_nat: nat;

    if Str2Int(sy@) == 0nat {
        result_nat = 1nat % modulo;
    } else {
        let nn: nat = n as nat;
        let mut i: nat = 0nat;
        let mut cur: nat = base;
        while i < nn
            invariant
                0nat <= i, i <= nn,
            decreases nn - i
        {
            cur = (cur * cur) % modulo;
            i = i + 1nat;
        }
        result_nat = cur;
    }

    if result_nat == 0nat {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: nat = result_nat;
    while tmp > 0nat
        invariant
            tmp >= 0nat,
        decreases tmp
    {
        if tmp % 2nat == 1nat { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2nat;
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
