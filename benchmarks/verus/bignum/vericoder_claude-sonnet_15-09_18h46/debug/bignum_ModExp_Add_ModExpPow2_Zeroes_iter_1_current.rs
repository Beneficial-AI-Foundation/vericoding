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
spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

spec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = mod_exp_helper(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * mod_exp_helper(base, exp - 1, modulus)) % modulus
    }
}

proof fn str2int_preserves_validity(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
}

proof fn exp_mod_equivalence(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus == mod_exp_helper(base, exp, modulus)
    decreases exp
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_val = mod_exp_helper(base, exp, modulus);
    
    let mut result = Vec::<char>::new();
    let mut temp = result_val;
    
    if temp == 0 {
        result.push('0');
    } else {
        while temp > 0
            invariant
                ValidBitString(result@),
                temp >= 0
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
    }
    
    proof {
        str2int_preserves_validity(sx@);
        str2int_preserves_validity(sy@);
        str2int_preserves_validity(sz@);
        exp_mod_equivalence(base, exp, modulus);
    }
    
    result
}
// </vc-code>

fn main() {}
}
