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
/* helper modified by LLM (iteration 4): fixed nat literal syntax and type conversions */
proof fn pow_mod_properties(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures Exp_int(base, exp) % modulus < modulus
{
}

proof fn str2int_valid_range(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
}

proof fn exp_base_cases(x: nat, y: nat)
    ensures y == 0 ==> Exp_int(x, y) == 1,
            y == 1 ==> Exp_int(x, y) == x
{
}

proof fn modular_arithmetic_lemma(a: nat, b: nat, m: nat)
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            c == '0' ==> result == 0,
            c == '1' ==> result == 1
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn is_zero_string(s: &[char]) -> (result: bool)
    requires ValidBitString(s@)
    ensures result == (Str2Int(s@) == 0)
{
    s.len() == 0 || s.iter().all(|&c| c == '0')
}

exec fn nat_to_binary_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            result@.len() > 0
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0nat
            invariant ValidBitString(result@)
            decreases temp
        {
            if temp % 2nat == 1nat {
                result.insert(0, '1');
            } else {
                result.insert(0, '0');
            }
            temp = temp / 2nat;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed nat literal syntax and type conversions throughout */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if is_zero_string(sy) {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        let base_val = Str2Int(sx@);
        let mod_val = Str2Int(sz@);
        let result_val = base_val % mod_val;
        
        return nat_to_binary_string(result_val);
    }
    
    let mut sy_half = Vec::new();
    let mut carry = 0nat;
    
    for i in 0..sy.len() {
        let digit_val = char_to_digit(sy[i]);
        let current = carry * 2nat + digit_val;
        sy_half.push(if current / 2nat == 1nat { '1' } else { '0' });
        carry = current % 2nat;
    }
    
    while sy_half.len() > 1 && sy_half[0] == '0' {
        sy_half.remove(0);
    }
    
    let half_result = ModExp_ModExpPow2_Mul(sx, &sy_half, sz);
    
    let squared_result = ModExp_ModExpPow2_Mul(&half_result, &['1'], sz);
    
    let is_odd = sy[sy.len() - 1] == '1';
    
    if is_odd {
        let base_mod = ModExp_ModExpPow2_Mul(sx, &['1'], sz);
        ModExp_ModExpPow2_Mul(&squared_result, &base_mod, sz)
    } else {
        squared_result
    }
}
// </vc-code>

fn main() {}
}
