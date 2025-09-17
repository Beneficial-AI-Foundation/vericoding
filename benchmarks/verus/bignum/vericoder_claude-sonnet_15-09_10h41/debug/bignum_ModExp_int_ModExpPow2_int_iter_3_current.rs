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
/* helper modified by LLM (iteration 3): fixed nat literal syntax by removing nat suffix */
fn char_to_digit(c: char) -> nat
    requires c == '0' || c == '1'
    ensures c == '0' ==> char_to_digit(c) == 0,
            c == '1' ==> char_to_digit(c) == 1
{
    if c == '1' { 1 } else { 0 }
}

fn digit_to_char(d: nat) -> char
    requires d == 0 || d == 1
    ensures d == 0 ==> digit_to_char(d) == '0',
            d == 1 ==> digit_to_char(d) == '1'
{
    if d == 1 { '1' } else { '0' }
}

fn nat_to_bitstring(n: nat) -> Vec<char>
    ensures ValidBitString(nat_to_bitstring(n)@),
            Str2Int(nat_to_bitstring(n)@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            let bit = if temp % 2 == 1 { '1' } else { '0' };
            result.push(bit);
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}

fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    ensures mod_exp_helper(base, exp, modulus) == Exp_int(base, exp) % modulus
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = mod_exp_helper(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * mod_exp_helper(base, exp - 1, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed helper function calls */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = mod_exp_helper(base, exp, modulus);
    let result_vec = nat_to_bitstring(result_nat);
    
    result_vec
}
// </vc-code>

fn main() {}
}
