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
/* helper modified by LLM (iteration 2): Fixed nat type mismatches by using nat literals and proper comparisons */
spec fn pow_mod_properties(base: nat, exp: nat, modulus: nat) -> bool
{
    modulus > 1 ==> (base % modulus < modulus && (base * base) % modulus == (base % modulus * base % modulus) % modulus)
}

proof fn exp_mod_correctness(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus < modulus
{
}

spec fn binary_to_nat_correct(s: Seq<char>) -> bool
{
    ValidBitString(s) ==> Str2Int(s) >= 0
}

exec fn char_to_digit(c: char) -> (result: u8)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            (c == '0') ==> result == 0,
            (c == '1') ==> result == 1
{
    if c == '1' { 1 } else { 0 }
}

exec fn nat_to_binary_string(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    let mut result = Vec::new();
    let mut temp = n;
    while temp > 0nat
        invariant ValidBitString(result@)
        decreases temp
    {
        if temp % 2nat == 1nat {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / 2nat;
    }
    result.reverse();
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed nat type mismatches by using nat literals for all numeric comparisons and operations */
{
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base_mod = Str2Int(sx@) % Str2Int(sz@);
    let mut result_val = 1nat;
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    let mut base = base_mod;
    let mut exp = exp_val;
    
    while exp > 0nat
        invariant
            mod_val > 1nat,
            result_val < mod_val,
            base < mod_val,
            (result_val * Exp_int(base, exp)) % mod_val == Exp_int(Str2Int(sx@), Str2Int(sy@)) % mod_val
        decreases exp
    {
        if exp % 2nat == 1nat {
            result_val = (result_val * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp = exp / 2nat;
    }
    
    nat_to_binary_string(result_val)
}
// </vc-code>

fn main() {}
}
