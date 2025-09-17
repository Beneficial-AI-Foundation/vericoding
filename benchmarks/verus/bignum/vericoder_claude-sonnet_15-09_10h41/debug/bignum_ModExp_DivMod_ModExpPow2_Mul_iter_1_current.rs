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
exec fn modular_exp(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    ensures modular_exp(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = modular_exp(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * modular_exp(base, exp - 1, modulus)) % modulus
    }
}

exec fn seq_to_string(s: &Seq<char>) -> String
    requires ValidBitString(*s)
{
    let mut result = String::new();
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
    {
        result.push(s.index(i as int));
        i += 1;
    }
    result
}

exec fn nat_to_binary_vec(mut n: nat) -> Vec<char>
    ensures ValidBitString(result@)
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        while n > 0
            invariant ValidBitString(result@)
        {
            if n % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            n = n / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = modular_exp(base, exp, modulus);
    let result_vec = nat_to_binary_vec(result_nat);
    
    result_vec
}
// </vc-code>

fn main() {}
}
