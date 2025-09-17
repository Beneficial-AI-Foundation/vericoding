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
exec fn Int2Str(x: nat) -> Vec<char>
{
    let mut res = Vec::new();
    let mut v = x;
    while v > 0
    {
        res.push(if v % 2 == 1 { '1' } else { '0' });
        v = v / 2;
    }
    res.reverse();
    if res.len() == 0 {
        res.push('0');
    }
    res
}

exec fn pow_mod(base: int, exp: Seq<char>, modulus: int) -> int
    decreases exp.len()
{
    if exp.len() == 0 {
        1
    } else {
        let half = pow_mod(base % modulus, exp.subrange(0, exp.len() - 1), modulus);
        let sq = (half * half) % modulus;
        if exp.index(exp.len() - 1) == '1' {
            (sq * (base % modulus)) % modulus
        } else {
            sq
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base_int = Str2Int(sx@);
    let modulus = Str2Int(sz@);
    let res_int = pow_mod(base_int, sy@, modulus);
    Int2Str(res_int as nat)
}
// </vc-code>

fn main() {}
}
