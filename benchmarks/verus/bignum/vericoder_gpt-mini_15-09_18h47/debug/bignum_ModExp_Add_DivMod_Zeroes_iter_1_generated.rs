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
fn seqslice_to_nat(s: &[char]) -> nat
    requires
        ValidBitString(s@),
    ensures
        result == Str2Int(s@),
{
    let mut i: usize = 0usize;
    let mut acc: nat = 0;
    while i < s.len()
        invariant
            acc >= 0,
        decreases
            s.len() - i
    {
        let bit = if s[i] == '1' { 1 } else { 0 };
        acc = acc * 2 + bit;
        i = i + 1usize;
    }
    acc
}

fn modpow(mut base: nat, mut exp: nat, m: nat) -> nat
    requires
        m > 0,
    ensures
        result < m,
{
    let mut res: nat = 1 % m;
    while exp > 0
        invariant
            res < m,
        decreases
            exp
    {
        if exp % 2 == 1 {
            res = (res * base) % m;
        }
        exp = exp / 2;
        base = (base * base) % m;
    }
    res
}

fn nat_to_bits(mut n: nat) -> Vec<char>
{
    let mut bits = Vec::<char>::new();
    if n == 0 {
        return bits;
    }
    while n > 0
        invariant
            bits.len() >= 0,
        decreases
            n
    {
        if n % 2 == 1 {
            bits.push('1');
        } else {
            bits.push('0');
        }
        n = n / 2;
    }
    let mut res = Vec::<char>::new();
    while bits.len() > 0
        invariant
            res.len() >= 0,
        decreases
            bits.len()
    {
        match bits.pop() {
            Some(ch) => res.push(ch),
            None => (),
        }
    }
    res
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
    let base = seqslice_to_nat(sx);
    let exp = seqslice_to_nat(sy);
    let m = seqslice_to_nat(sz);
    let r = modpow(base % m, exp, m);
    return nat_to_bits(r);
}
// </vc-code>

fn main() {}
}
