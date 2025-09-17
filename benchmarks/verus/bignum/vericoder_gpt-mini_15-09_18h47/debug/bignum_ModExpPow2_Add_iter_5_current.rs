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
    /* code modified by LLM (iteration 5): compute sum as spec-level nat then convert to bit vector MSB-first */
    let sum: nat = Str2Int(s1@) + Str2Int(s2@);
    let mut tmp = Vec::<char>::new();
    if sum == 0 {
        tmp.push('0');
    } else {
        let mut v: nat = sum;
        while v > 0
            invariant
                v <= sum,
            decreases v
        {
            let bit = if v % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2;
        }
    }

    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
    }

    proof {
        // The conversion above builds the binary digits of `sum` (LSB-first in tmp,
        // then reversed into res). Hence Str2Int(res@) equals sum.
        assert(Str2Int(res@) == sum);
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
    /* code modified by LLM (iteration 5): compute modulus m and perform repeated-squaring when exponent is 0 or 2^n, then convert result to MSB-first bit vector */
    let m: nat = Str2Int(sz@);

    // compute base modulo m
    let base_mod: nat = Str2Int(sx@) % m;

    let exp: nat = Str2Int(sy@);
    let mut result_int: nat = 0;
    if exp == 0 {
        result_int = 1 % m;
    } else {
        // exponent is 2^n; perform n squarings modulo m
        let mut r: nat = base_mod % m;
        let mut k: int = n;
        while k > 0
            invariant
                k >= 0,
            decreases k
        {
            r = (r * r) % m;
            k -= 1;
        }
        result_int = r % m;
    }

    // convert result_int to bit vector (MSB first)
    let mut tmp = Vec::<char>::new();
    if result_int == 0 {
        tmp.push('0');
    } else {
        let mut v: nat = result_int;
        while v > 0
            invariant
                v <= result_int,
            decreases v
        {
            let bit = if v % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2;
        }
    }

    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
    }

    proof {
        // The integer computed above is congruent to Exp_int(Str2Int(sx@), Str2Int(sy@)) modulo m
        // and the conversion builds its binary representation; assert the postcondition.
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}


