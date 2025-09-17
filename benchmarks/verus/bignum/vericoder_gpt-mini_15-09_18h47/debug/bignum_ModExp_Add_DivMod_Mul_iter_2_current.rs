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
    /* code modified by LLM (iteration 2): convert two bitstrings to nat, add, and convert back to bitstring */
    let mut a: nat = 0nat;
    for i in 0..s1.len() {
        let c = s1[i];
        a = a * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let mut b: nat = 0nat;
    for i in 0..s2.len() {
        let c = s2[i];
        b = b * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let sum: nat = a + b;
    let mut res: Vec<char> = Vec::new();
    if sum != 0nat {
        let mut tmp: nat = sum;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0nat {
            bits.push(if tmp % 2nat == 1nat { '1' } else { '0' });
            tmp = tmp / 2nat;
        }
        let mut i: usize = bits.len();
        while i > 0 {
            i = i - 1;
            res.push(bits[i]);
        }
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
    /* code modified by LLM (iteration 2): compute quotient and remainder as nats then convert to bitstrings */
    let mut dv: nat = 0nat;
    for i in 0..dividend.len() {
        let c = dividend[i];
        dv = dv * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let mut ds: nat = 0nat;
    for i in 0..divisor.len() {
        let c = divisor[i];
        ds = ds * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let q: nat = dv / ds;
    let r: nat = dv % ds;

    fn nat_to_bits(mut v: nat) -> Vec<char> {
        let mut out: Vec<char> = Vec::new();
        if v == 0nat {
            return out;
        }
        let mut bits: Vec<char> = Vec::new();
        while v > 0nat {
            bits.push(if v % 2nat == 1nat { '1' } else { '0' });
            v = v / 2nat;
        }
        let mut i: usize = bits.len();
        while i > 0 {
            i = i - 1;
            out.push(bits[i]);
        }
        out
    }

    (nat_to_bits(q), nat_to_bits(r))
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): multiply two bitstrings by converting to nat, multiply, and convert back */
    let mut a: nat = 0nat;
    for i in 0..s1.len() {
        let c = s1[i];
        a = a * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let mut b: nat = 0nat;
    for i in 0..s2.len() {
        let c = s2[i];
        b = b * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let prod: nat = a * b;

    let mut res: Vec<char> = Vec::new();
    if prod != 0nat {
        let mut tmp: nat = prod;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0nat {
            bits.push(if tmp % 2nat == 1nat { '1' } else { '0' });
            tmp = tmp / 2nat;
        }
        let mut i: usize = bits.len();
        while i > 0 {
            i = i - 1;
            res.push(bits[i]);
        }
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
    /* code modified by LLM (iteration 2): compute modular exponentiation by converting inputs to nats and performing repeated modular multiplication */
    let mut x: nat = 0nat;
    for i in 0..sx.len() {
        let c = sx[i];
        x = x * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let mut y: nat = 0nat;
    for i in 0..sy.len() {
        let c = sy[i];
        y = y * 2nat + if c == '1' { 1nat } else { 0nat };
    }
    let mut m: nat = 0nat;
    for i in 0..sz.len() {
        let c = sz[i];
        m = m * 2nat + if c == '1' { 1nat } else { 0nat };
    }

    let mut res_n: nat = 1nat;
    let mut i: nat = 0nat;
    while i < y {
        res_n = (res_n * x) % m;
        i = i + 1nat;
    }

    let mut res: Vec<char> = Vec::new();
    if res_n != 0nat {
        let mut tmp: nat = res_n;
        let mut bits: Vec<char> = Vec::new();
        while tmp > 0nat {
            bits.push(if tmp % 2nat == 1nat { '1' } else { '0' });
            tmp = tmp / 2nat;
        }
        let mut j: usize = bits.len();
        while j > 0 {
            j = j - 1;
            res.push(bits[j]);
        }
    }
    res
}
// </vc-code>

fn main() {}
}
