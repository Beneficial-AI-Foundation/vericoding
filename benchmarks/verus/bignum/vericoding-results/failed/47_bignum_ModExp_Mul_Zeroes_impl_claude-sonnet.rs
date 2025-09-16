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
/* helper modified by LLM (iteration 10): Using usize instead of nat for exec functions */
exec fn char_to_usize(c: char) -> usize
    requires c == '0' || c == '1'
    ensures c == '0' ==> char_to_usize(c) == 0,
            c == '1' ==> char_to_usize(c) == 1
{
    if c == '0' { 0 } else { 1 }
}

exec fn usize_to_char(n: usize) -> char
    requires n == 0 || n == 1
    ensures n == 0 ==> usize_to_char(n) == '0',
            n == 1 ==> usize_to_char(n) == '1'
{
    if n == 0 { '0' } else { '1' }
}

exec fn multiply_mod_usize(a: usize, b: usize, m: usize) -> usize
    requires m > 1
    ensures multiply_mod_usize(a, b, m) == (a * b) % m
{
    (a * b) % m
}

exec fn nat_to_vec_char(n: nat) -> Vec<char>
    ensures ValidBitString(nat_to_vec_char(n)@),
            Str2Int(nat_to_vec_char(n)@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
    } else {
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            result.push(if temp % 2 == 0 { '0' } else { '1' });
            temp = temp / 2;
        }
        result.reverse();
    }
    result
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
    /* code modified by LLM (iteration 10): Using spec functions and nat_to_vec_char helper */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_prefix = &sy[0..sy.len()-1];
    
    let half_result = ModExp_Mul_Zeroes(sx, sy_prefix, sz);
    let squared = (Str2Int(half_result@) * Str2Int(half_result@)) % Str2Int(sz@);
    
    let final_result = if last_bit == '1' {
        (squared * Str2Int(sx@)) % Str2Int(sz@)
    } else {
        squared
    };
    
    nat_to_vec_char(final_result)
}
// </vc-code>

fn main() {}
}
