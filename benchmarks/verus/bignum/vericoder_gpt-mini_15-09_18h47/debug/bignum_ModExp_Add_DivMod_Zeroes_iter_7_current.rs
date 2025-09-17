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

// <vc-helpers>
/* helper modified by LLM (iteration 7): convert Seq<char> to nat (spec) */
spec fn SeqBits_to_nat(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * SeqBits_to_nat(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }) }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 7): compute modular exponentiation and convert to bit vector */
    let mut idx_b: usize = 0usize;
    let mut base: nat = 0;
    while idx_b < sx.len()
        invariant
            idx_b <= sx.len(),
        decreases sx.len() - idx_b
    {
        base = base * 2 + if sx[idx_b] == '1' { 1 } else { 0 };
        idx_b += 1;
    }

    let mut idx_e: usize = 0usize;
    let mut exp: nat = 0;
    while idx_e < sy.len()
        invariant
            idx_e <= sy.len(),
        decreases sy.len() - idx_e
    {
        exp = exp * 2 + if sy[idx_e] == '1' { 1 } else { 0 };
        idx_e += 1;
    }

    let mut idx_m: usize = 0usize;
    let mut m: nat = 0;
    while idx_m < sz.len()
        invariant
            idx_m <= sz.len(),
        decreases sz.len() - idx_m
    {
        m = m * 2 + if sz[idx_m] == '1' { 1 } else { 0 };
        idx_m += 1;
    }

    let mut base_v: nat = if m == 0 { 0 } else { base % m };
    let mut exp_v: nat = exp;
    let mut res_v: nat = if m == 0 { 0 } else { 1 % m };
    while exp_v > 0
        invariant
            m > 0,
        decreases exp_v
    {
        if exp_v % 2 == 1 {
            res_v = (res_v * base_v) % m;
        }
        exp_v = exp_v / 2;
        base_v = (base_v * base_v) % m;
    }

    let mut bits = Vec::<char>::new();
    let mut tmp: nat = res_v;
    if tmp == 0 {
        return bits;
    }
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 { bits.push('1'); } else { bits.push('0'); }
        tmp = tmp / 2;
    }
    let mut res_vec = Vec::<char>::new();
    while bits.len() > 0
        invariant
            bits.len() >= 0usize,
        decreases bits.len()
    {
        match bits.pop() {
            Some(ch) => res_vec.push(ch),
            None => (),
        }
    }
    res_vec
}
// </vc-code>

fn main() {}
}
