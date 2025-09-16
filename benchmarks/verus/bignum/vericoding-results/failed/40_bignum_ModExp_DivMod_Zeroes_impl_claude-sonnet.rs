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
/* helper modified by LLM (iteration 10): fixed all nat literals and type annotations */
spec fn pow_mod(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1nat
    decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else if exp % 2nat == 0nat {
        let half = pow_mod(base, exp / 2nat, modulus);
        (half * half) % modulus
    } else {
        (base * pow_mod(base, (exp - 1nat) as nat, modulus)) % modulus
    }
}

proof fn exp_int_eq_pow_mod(base: nat, exp: nat, modulus: nat)
    requires modulus > 1nat
    ensures Exp_int(base, exp) % modulus == pow_mod(base, exp, modulus)
    decreases exp
{
}

fn int_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0nat
            invariant ValidBitString(result@)
            decreases num
        {
            if num % 2nat == 1nat {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2nat;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed all nat literals and type annotations */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    if exp == 0nat {
        return vec!['1'];
    }
    
    let mut result: nat = 1nat;
    let mut base_mod = base % modulus;
    let mut exp_remaining = exp;
    
    while exp_remaining > 0nat
        invariant ValidBitString(sx@),
                  ValidBitString(sy@),
                  ValidBitString(sz@),
                  modulus > 1nat,
                  result < modulus
        decreases exp_remaining
    {
        if exp_remaining % 2nat == 1nat {
            result = (result * base_mod) % modulus;
        }
        base_mod = (base_mod * base_mod) % modulus;
        exp_remaining = exp_remaining / 2nat;
    }
    
    int_to_bit_string(result)
}
// </vc-code>

fn main() {}
}
