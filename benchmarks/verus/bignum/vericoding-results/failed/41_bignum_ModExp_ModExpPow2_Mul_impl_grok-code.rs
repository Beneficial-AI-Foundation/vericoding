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
fn mod_mul(a: int, b: int, m: int) -> int
requires
    m > 0,
ensures
    mod_mul(a, b, m) == (a * b) % m,
{
    let a_mod = a % m;
    let b_mod = b % m;
    (a_mod * b_mod) % m
}

fn str_to_nat(s: &[char]) -> nat
requires
    ValidBitString(s@),
ensures
    str_to_nat(s) == Str2Int(s@),
{
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            acc == Str2Int(s@.subrange(0, i as int)),
            0 <= i <= s.len(),
        decreases s.len() - i
    {
        acc = acc * 2;
        if s[i] == '1' {
            acc = acc + 1;
        }
        i += 1;
    }
    acc
}

fn mod_exp(mut base: int, mut e: int, m: int) -> int
requires
    m > 0,
ensures
    mod_exp(base, e, m) == Exp_int(base, e) % m,
{
    let mut result: int = 1;
    base = base % m;
    while e > 0
        invariant
            0 <= e,
        decreases e
    {
        if e % 2 == 1 {
            result = mod_mul(result, base, m);
        }
        base = mod_mul(base, base, m);
        e = e / 2;
    }
    result
}

fn nat_to_binary(n: nat) -> Vec<char>
ensures
    ValidBitString(result@),
    Str2Int(result@) == n,
{
    if n == 0 {
        return vec!['0'];
    }
    let mut bits: Vec<char> = Vec::new();
    let mut current = n;
    while current > 0
        invariant
            current >= 0,
            bits.len() >= 0,
        decreases current
    {
        let bit = if (current % 2) == 1 { '1' } else { '0' };
        bits.push(bit);
        current = current / 2;
    }
    bits.reverse();
    bits
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m_nat = str_to_nat(sz);
    let x_nat = str_to_nat(sx);
    let y_nat = str_to_nat(sy);
    let result_mod = mod_exp(x_nat, y_nat, m_nat);
    let res_binary = nat_to_binary(result_mod);
    res_binary
}
// </vc-code>

fn main() {}
}
