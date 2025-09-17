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
/* helper modified by LLM (iteration 3): convert slice of bits to nat */
fn seqslice_to_nat(s: &[char]) -> nat {
    let mut i: nat = 0nat;
    let mut acc: nat = 0nat;
    while i < (s.len() as nat)
        invariant
            acc >= 0nat,
            i <= s.len() as nat,
        decreases
            (s.len() as nat) - i
    {
        let bit: nat = if s[i as usize] == '1' { 1nat } else { 0nat };
        acc = acc * 2nat + bit;
        i = i + 1nat;
    }
    acc
}

/* helper modified by LLM (iteration 3): modular exponentiation by squaring */
fn modpow(mut base: nat, mut exp: nat, m: nat) -> nat
    requires
        m > 0nat,
{
    base = base % m;
    let mut res: nat = 1nat % m;
    while exp > 0nat
        invariant
            res < m,
        decreases
            exp
    {
        if exp % 2nat == 1nat {
            res = (res * base) % m;
        }
        exp = exp / 2nat;
        base = (base * base) % m;
    }
    res
}

/* helper modified by LLM (iteration 3): convert nat to bit vector (MSB first) */
fn nat_to_bits(mut n: nat) -> Vec<char> {
    let mut bits = Vec::<char>::new();
    if n == 0nat {
        return bits;
    }
    while n > 0nat
        decreases
            n
    {
        if n % 2nat == 1nat {
            bits.push('1');
        } else {
            bits.push('0');
        }
        n = n / 2nat;
    }
    let mut res = Vec::<char>::new();
    while bits.len() > 0usize
        decreases
            bits.len() as nat
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
/* code modified by LLM (iteration 3): compute modular exponentiation and return its bit-vector representation */
    let base: nat = seqslice_to_nat(sx);
    let exp: nat = seqslice_to_nat(sy);
    let m: nat = seqslice_to_nat(sz);
    let r: nat = modpow(base % m, exp, m);
    return nat_to_bits(r);
}
// </vc-code>

fn main() {}
}
