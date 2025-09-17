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
/* helper modified by LLM (iteration 2): Fixed type mismatches for nat operations */
exec fn char_to_nat(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            c == '0' ==> result == 0,
            c == '1' ==> result == 1
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn nat_to_char(n: nat) -> (result: char)
    requires n == 0 || n == 1
    ensures result == '0' || result == '1',
            n == 0 ==> result == '0',
            n == 1 ==> result == '1'
{
    if n == 1nat { '1' } else { '0' }
}

exec fn mod_exp_simple(base: nat, exp: nat, modulus: nat) -> (result: nat)
    requires modulus > 1
    ensures result == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else {
        (base * mod_exp_simple(base, exp - 1nat, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches for nat operations */
    let base = Str2Int(sx@);
    let exponent = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = mod_exp_simple(base, exponent, modulus);
    
    let mut result = Vec::<char>::new();
    
    if result_nat == 0nat {
        result.push('0');
    } else {
        let mut temp = result_nat;
        while temp > 0nat
            invariant ValidBitString(result@)
        {
            let bit = temp % 2nat;
            result.push(nat_to_char(bit));
            temp = temp / 2nat;
        }
        result.reverse();
    }
    
    result
}
// </vc-code>

fn main() {}
}
