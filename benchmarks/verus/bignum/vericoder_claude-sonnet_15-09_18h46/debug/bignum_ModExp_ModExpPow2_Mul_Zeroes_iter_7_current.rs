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
/* helper modified by LLM (iteration 7): Fixed nat literal syntax by removing nat suffixes */
fn binary_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i += 1;
    }
    result
}

fn nat_to_binary(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
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

fn mod_exp(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1
    ensures result == Exp_int(base, exp) % modulus
{
    if exp == 0 {
        1 % modulus
    } else {
        let mut result = 1;
        let mut base_power = base % modulus;
        let mut remaining_exp = exp;
        
        while remaining_exp > 0
            invariant
                modulus > 1,
                result < modulus,
                base_power < modulus
        {
            if remaining_exp % 2 == 1 {
                result = (result * base_power) % modulus;
            }
            base_power = (base_power * base_power) % modulus;
            remaining_exp = remaining_exp / 2;
        }
        result
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
/* code modified by LLM (iteration 7): Fixed nat literal syntax by removing nat suffixes */
{
    let x = binary_to_nat(sx);
    let y = binary_to_nat(sy);
    let z = binary_to_nat(sz);
    
    let result_nat = mod_exp(x, y, z);
    let result_vec = nat_to_binary(result_nat);
    
    result_vec
}
// </vc-code>

fn main() {}
}
