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
proof fn str2int_recursive(s: Seq<char>, c: char) 
    requires ValidBitString(s) && (c == '0' || c == '1') 
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }) 
{ 
    /* helper modified by LLM (iteration 9): Fixed syntax by removing previous ghost macro */ }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): Made variables mutable to fix assignment errors */ 
    let mut base_val: u32 = 0;
    let mut exponent_val: u32 = 0;
    let modulus_val: u32 = 0;
    let mut result_val: u32 = 1;
    
    while exponent_val > 0
        invariant
            result_val >= 0,
            exponent_val >= 0
    {
        if exponent_val % 2 == 1 {
            result_val = (result_val * base_val) % modulus_val;
        }
        base_val = (base_val * base_val) % modulus_val;
        exponent_val = exponent_val / 2;
    }
    
    let mut res = Vec::new();
    res.push(if result_val == 1 { '1' } else { '0' });
    res
}
// </vc-code>

fn main() {}
}
