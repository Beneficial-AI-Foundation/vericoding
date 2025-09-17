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
/* helper modified by LLM (iteration 5): removed nat suffixes causing compilation errors */
spec fn modular_exp_helper(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = modular_exp_helper(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * modular_exp_helper(base, (exp - 1) as nat, modulus)) % modulus
    }
}

spec fn int_to_bit_string_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        let digit = if n % 2 == 0 { '0' } else { '1' };
        int_to_bit_string_helper(n / 2, seq![digit] + acc)
    }
}

exec fn int_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 0 {
                result.insert(0, '0');
            } else {
                result.insert(0, '1');
            }
            temp = temp / 2;
        }
        result
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
    /* code modified by LLM (iteration 5): removed nat suffixes causing compilation errors */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let mut result_val = 1;
    let mut base_val = base % modulus;
    let mut exp_val = exp;
    
    while exp_val > 0
        invariant ValidBitString(sx@),
                  ValidBitString(sy@),
                  ValidBitString(sz@),
                  modulus > 1,
                  result_val < modulus,
                  base_val < modulus
    {
        if exp_val % 2 == 1 {
            result_val = (result_val * base_val) % modulus;
        }
        base_val = (base_val * base_val) % modulus;
        exp_val = exp_val / 2;
    }
    
    int_to_bit_string(result_val)
}
// </vc-code>

fn main() {}
}
