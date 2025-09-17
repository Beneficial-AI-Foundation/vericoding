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
/* helper modified by LLM (iteration 2): Fixed type mismatches by using nat literals and proper casting */
spec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1nat } else { 0nat }
}

spec fn seq_to_string_invariant(s: Seq<char>, result: nat, processed: nat) -> bool
{
    result == Str2Int(s.subrange(0, processed as int))
}

exec fn binary_string_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2nat + char_to_nat(s[i]);
        i += 1;
    }
    result
}

exec fn nat_to_binary_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0nat {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    let mut result = Vec::new();
    let mut temp = n;
    while temp > 0nat
        invariant temp >= 0nat
    {
        if temp % 2nat == 0nat {
            result.insert(0, '0');
        } else {
            result.insert(0, '1');
        }
        temp = temp / 2nat;
    }
    result
}

exec fn mod_exp(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1nat
    ensures result == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else if exp % 2nat == 0nat {
        let half_exp = mod_exp(base, exp / 2nat, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * mod_exp(base, exp - 1nat, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed implementation using helper functions */
{
    let base = binary_string_to_nat(sx);
    let exp = binary_string_to_nat(sy);
    let modulus = binary_string_to_nat(sz);
    
    let result_nat = mod_exp(base, exp, modulus);
    let result = nat_to_binary_string(result_nat);
    
    result
}
// </vc-code>

fn main() {}
}
