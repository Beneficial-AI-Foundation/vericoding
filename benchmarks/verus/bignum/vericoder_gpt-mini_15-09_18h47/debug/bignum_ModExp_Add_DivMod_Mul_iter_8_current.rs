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
    /* code modified by LLM (iteration 8): binary addition using carry and reversing temporary buffer */
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut carry: u8 = 0;
    let mut tmp: Vec<char> = Vec::<char>::new();

    while i > 0 || j > 0 || carry != 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
    decreases i + j + (carry as usize)
    {
        let bi: u8 = if i > 0 { if s1[i - 1] == '1' { 1 } else { 0 } } else { 0 };
        let bj: u8 = if j > 0 { if s2[j - 1] == '1' { 1 } else { 0 } } else { 0 };
        let sum: u8 = bi + bj + carry;
        tmp.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
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
    /* code modified by LLM (iteration 8): convert bitstrings to u128, compute quotient and remainder, convert back to bitstrings */
    let mut dv: u128 = 0u128;
    for idx in 0..dividend.len() {
        let c = dividend[idx];
        dv = dv.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }
    let mut ds: u128 = 0u128;
    for idx in 0..divisor.len() {
        let c = divisor[idx];
        ds = ds.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }

    // divisor precondition ensures ds > 0
    let q: u128 = dv / ds;
    let r: u128 = dv % ds;

    // convert q to bits
    let mut qres_tmp: Vec<char> = Vec::<char>::new();
    if q != 0u128 {
        let mut tmp: u128 = q;
        while tmp > 0u128
            invariant
                tmp >= 0u128,
        decreases tmp
        {
            qres_tmp.push(if tmp % 2u128 == 1u128 { '1' } else { '0' });
            tmp = tmp / 2u128;
        }
    }
    let mut qres: Vec<char> = Vec::<char>::new();
    let mut i_nat: usize = qres_tmp.len();
    while i_nat > 0
        invariant
            i_nat <= qres_tmp.len(),
    decreases i_nat
    {
        i_nat -= 1;
        qres.push(qres_tmp[i_nat]);
    }

    // convert r to bits
    let mut rres_tmp: Vec<char> = Vec::<char>::new();
    if r != 0u128 {
        let mut tmp: u128 = r;
        while tmp > 0u128
            invariant
                tmp >= 0u128,
        decreases tmp
        {
            rres_tmp.push(if tmp % 2u128 == 1u128 { '1' } else { '0' });
            tmp = tmp / 2u128;
        }
    }
    let mut rres: Vec<char> = Vec::<char>::new();
    let mut j_nat: usize = rres_tmp.len();
    while j_nat > 0
        invariant
            j_nat <= rres_tmp.len(),
    decreases j_nat
    {
        j_nat -= 1;
        rres.push(rres_tmp[j_nat]);
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
    /* code modified by LLM (iteration 8): multiply by converting to u128, multiply, and convert result to bitstring */
    let mut a: u128 = 0u128;
    for idx in 0..s1.len() {
        let c = s1[idx];
        a = a.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }
    let mut b: u128 = 0u128;
    for idx in 0..s2.len() {
        let c = s2[idx];
        b = b.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }
    let prod: u128 = a.wrapping_mul(b);

    let mut res_tmp: Vec<char> = Vec::<char>::new();
    if prod != 0u128 {
        let mut tmp: u128 = prod;
        while tmp > 0u128
            invariant
                tmp >= 0u128,
        decreases tmp
        {
            res_tmp.push(if tmp % 2u128 == 1u128 { '1' } else { '0' });
            tmp = tmp / 2u128;
        }
    }
    let mut res: Vec<char> = Vec::<char>::new();
    let mut i_nat: usize = res_tmp.len();
    while i_nat > 0
        invariant
            i_nat <= res_tmp.len(),
    decreases i_nat
    {
        i_nat -= 1;
        res.push(res_tmp[i_nat]);
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
    /* code modified by LLM (iteration 8): modular exponentiation by converting to u128 and using repeated-squaring, then convert result to bitstring */
    let mut x: u128 = 0u128;
    for idx in 0..sx.len() {
        let c = sx[idx];
        x = x.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }
    let mut y: u128 = 0u128;
    for idx in 0..sy.len() {
        let c = sy[idx];
        y = y.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }
    let mut m: u128 = 0u128;
    for idx in 0..sz.len() {
        let c = sz[idx];
        m = m.wrapping_mul(2u128).wrapping_add(if c == '1' { 1u128 } else { 0u128 });
    }

    // m > 1 by precondition
    let mut result: u128 = 1u128;
    let mut base: u128 = if m != 0u128 { x % m } else { 0u128 };
    let mut exp: u128 = y;
    while exp > 0u128
        invariant
            exp >= 0u128,
    decreases exp
    {
        if exp % 2u128 == 1u128 {
            result = (result.wrapping_mul(base)) % m;
        }
        base = (base.wrapping_mul(base)) % m;
        exp = exp / 2u128;
    }

    let mut res_tmp: Vec<char> = Vec::<char>::new();
    if result != 0u128 {
        let mut tmp: u128 = result;
        while tmp > 0u128
            invariant
                tmp >= 0u128,
        decreases tmp
        {
            res_tmp.push(if tmp % 2u128 == 1u128 { '1' } else { '0' });
            tmp = tmp / 2u128;
        }
    }
    let mut res: Vec<char> = Vec::<char>::new();
    let mut j: usize = res_tmp.len();
    while j > 0
        invariant
            j <= res_tmp.len(),
    decreases j
    {
        j -= 1;
        res.push(res_tmp[j]);
    }
    res
}

// </vc-code>

fn main() {}
}
