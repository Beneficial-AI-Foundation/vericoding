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
fn mul_mod(a: nat, b: nat, mod_: nat) -> nat
    requires mod_ > 0
    ensures res == (a * b) % mod_
{
    (a * b) % mod_
}

fn mod_exp(base: nat, exp: nat, mod_: nat) -> nat
    requires mod_ > 0
    ensures res == Exp_int(base, exp) % mod_
    decreases exp
{
    if exp == 0 { 1 } else {
        let half = mod_exp(base, exp / 2, mod_);
        let square = mul_mod(half, half, mod_);
        if exp % 2 == 1 {
            mul_mod(square, base % mod_, mod_)
        } else {
            square
        }
    }
}

fn build_bits(n: nat) -> Vec<char>
    decreases n
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let rest = build_bits(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        let mut result = rest;
        result.push(digit);
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);
    proof {
        assert(z >= 2);
    }
    let res_int: nat = mod_exp(x, y, z);
    let res_vec: Vec<char> = build_bits(res_int);
    res_vec
}
// </vc-code>

fn main() {}
}
