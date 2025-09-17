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
/* helper modified by LLM (iteration 2): Fixed type mismatches by using proper nat literals and type annotations */
exec fn char_to_nat(c: char) -> nat
    requires c == '0' || c == '1'
    ensures c == '0' ==> char_to_nat(c) == 0,
            c == '1' ==> char_to_nat(c) == 1
{
    if c == '0' { 0nat } else { 1nat }
}

exec fn nat_to_char(n: nat) -> char
    requires n == 0 || n == 1
    ensures n == 0 ==> nat_to_char(n) == '0',
            n == 1 ==> nat_to_char(n) == '1'
{
    if n == 0nat { '0' } else { '1' }
}

exec fn multiply_mod(a: nat, b: nat, m: nat) -> nat
    requires m > 1
    ensures multiply_mod(a, b, m) == (a * b) % m
{
    (a * b) % m
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches by using proper nat literals */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_prefix = &sy[0..sy.len()-1];
    
    let half_result = ModExp_Mul_Zeroes(sx, sy_prefix, sz);
    let squared = multiply_mod(Str2Int(half_result@), Str2Int(half_result@), Str2Int(sz@));
    
    let final_result = if last_bit == '1' {
        multiply_mod(squared, Str2Int(sx@), Str2Int(sz@))
    } else {
        squared
    };
    
    let mut result = Vec::new();
    let mut temp = final_result;
    if temp == 0nat {
        result.push('0');
    } else {
        while temp > 0nat {
            result.push(nat_to_char(temp % 2nat));
            temp = temp / 2nat;
        }
        result.reverse();
    }
    
    result
}
// </vc-code>

fn main() {}
}
