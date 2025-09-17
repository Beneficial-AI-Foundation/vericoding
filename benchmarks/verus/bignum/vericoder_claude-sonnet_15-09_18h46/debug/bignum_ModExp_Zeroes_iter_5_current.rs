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
/* helper modified by LLM (iteration 5): Fixed nat literal syntax errors */
exec fn char_to_nat(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
        c == '0' ==> result == 0,
        c == '1' ==> result == 1
{
    if c == '1' { 1 } else { 0 }
}

exec fn nat_to_char(n: nat) -> (result: char)
    requires n == 0 || n == 1
    ensures result == '0' || result == '1',
        n == 0 ==> result == '0',
        n == 1 ==> result == '1'
{
    if n == 1 { '1' } else { '0' }
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1
    ensures result == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half_exp = exp / 2;
        let half_result = mod_exp_helper(base, half_exp, modulus);
        let squared = (half_result * half_result) % modulus;
        if exp % 2 == 1 {
            (squared * base) % modulus
        } else {
            squared
        }
    }
}

exec fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
            decreases temp
        {
            let bit = temp % 2;
            result.push(nat_to_char(bit));
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat literal syntax errors */
    let base_int = Str2Int(sx@);
    let exp_int = Str2Int(sy@);
    let mod_int = Str2Int(sz@);
    
    let result_int = mod_exp_helper(base_int, exp_int, mod_int);
    let result_vec = nat_to_bit_string(result_int);
    
    result_vec
}
// </vc-code>

fn main() {}
}
