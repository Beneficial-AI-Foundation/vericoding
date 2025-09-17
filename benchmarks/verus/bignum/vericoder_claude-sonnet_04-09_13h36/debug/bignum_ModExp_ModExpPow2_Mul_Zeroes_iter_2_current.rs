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
exec fn str_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2nat;
        if s[i] == '1' {
            result = result + 1nat;
        }
        i = i + 1;
    }
    result
}

exec fn int_to_str(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut digits = Vec::new();
    while n > 0nat
        invariant ValidBitString(digits@)
    {
        if n % 2nat == 0nat {
            digits.push('0');
        } else {
            digits.push('1');
        }
        n = n / 2nat;
    }
    
    let mut result = Vec::new();
    let mut i = digits.len();
    while i > 0
        invariant ValidBitString(result@)
    {
        i = i - 1;
        result.push(digits[i]);
    }
    result
}

exec fn mod_mul(a: nat, b: nat, m: nat) -> (res: nat)
    requires m > 0
    ensures res == (a * b) % m
{
    (a * b) % m
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 0
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else if exp % 2nat == 0nat {
        let half_exp = mod_exp_helper(base, exp / 2nat, modulus);
        mod_mul(half_exp, half_exp, modulus)
    } else {
        let base_mod = base % modulus;
        let rest = mod_exp_helper(base, exp - 1nat, modulus);
        mod_mul(base_mod, rest, modulus)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = str_to_int(sx);
    let y = str_to_int(sy);
    let z = str_to_int(sz);
    
    let result_int = mod_exp_helper(x, y, z);
    let result = int_to_str(result_int);
    
    result
}
// </vc-code>

fn main() {}
}