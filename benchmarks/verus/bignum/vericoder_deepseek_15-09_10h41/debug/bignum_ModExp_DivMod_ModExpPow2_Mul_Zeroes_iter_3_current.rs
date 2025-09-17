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
/* helper modified by LLM (iteration 3): Fixed int_to_bitstring return type and ensures clause */
fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut num = n;
    let mut digits = Vec::new();
    while num > 0
        invariant 
            digits@.len() >= 0,
            forall |i| 0 <= i < digits@.len() ==> (digits@[i] == '0' || digits@[i] == '1')
        decreases num
    {
        if num % 2 == 1 {
            digits.push('1');
        } else {
            digits.push('0');
        }
        num = num / 2;
    }
    digits.reverse();
    digits
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added missing result variable and proper type annotations */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if y_val == 0 {
        let one: Vec<char> = vec!['1'];
        assert(Str2Int(one@) == 1);
        assert(1 % z_val == 1 % z_val);
        return one;
    }
    
    let mut result: nat = 1;
    let mut base: nat = x_val % z_val;
    let mut exponent: nat = y_val;
    
    while exponent > 0
        invariant
            result >= 0,
            base >= 0,
            exponent >= 0
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exponent = exponent / 2;
    }
    
    let res_vec: Vec<char> = int_to_bitstring(result);
    res_vec
}
// </vc-code>

fn main() {}
}
