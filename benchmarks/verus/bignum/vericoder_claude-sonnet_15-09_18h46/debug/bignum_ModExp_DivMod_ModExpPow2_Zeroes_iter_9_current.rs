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
/* helper modified by LLM (iteration 9): removed nat suffix from literals and used proper casting */
spec fn pow_mod_properties(base: nat, exp: nat, modulus: nat) -> bool
{
    modulus > 1 ==> (base % modulus < modulus && (base * base) % modulus == (base % modulus * base % modulus) % modulus)
}

proof fn exp_mod_correctness(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus < modulus
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, exp) == 1);
        assert(1 % modulus < modulus);
    } else {
        exp_mod_correctness(base, (exp - 1) as nat, modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

spec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}

exec fn str_to_nat_impl(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = &s[0..s.len()-1];
        let last_char = s[s.len()-1];
        let prefix_val = str_to_nat_impl(prefix);
        let last_bit = if last_char == '1' { 1 as nat } else { 0 as nat };
        2 * prefix_val + last_bit
    }
}

exec fn nat_to_str_impl(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): removed nat suffix from literals and used proper casting */
    let base = str_to_nat_impl(sx);
    let exp = str_to_nat_impl(sy);
    let modulus = str_to_nat_impl(sz);
    
    proof {
        exp_mod_correctness(base, exp, modulus);
    }
    
    let mut result_val = 1 as nat;
    let mut current_base = base % modulus;
    let mut remaining_exp = exp;
    
    while remaining_exp > 0
        invariant
            modulus > 1,
            result_val < modulus,
            current_base < modulus,
            (result_val * Exp_int(current_base, remaining_exp)) % modulus == Exp_int(base, exp) % modulus
        decreases remaining_exp
    {
        if remaining_exp % 2 == 1 {
            result_val = (result_val * current_base) % modulus;
        }
        current_base = (current_base * current_base) % modulus;
        remaining_exp = remaining_exp / 2;
    }
    
    nat_to_str_impl(result_val)
}
// </vc-code>

fn main() {}
}
