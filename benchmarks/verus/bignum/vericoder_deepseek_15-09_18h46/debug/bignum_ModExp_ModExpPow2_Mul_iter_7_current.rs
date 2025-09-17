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
/* helper modified by LLM (iteration 7): Removed problematic nat_to_u64 proof function */
fn u64_to_bitvec(mut n: u64) -> Vec<char>
    ensures ValidBitString(result@)
    ensures Str2Int(result@) == n as nat
{
    let mut res_vec = Vec::new();
    
    if n == 0 {
        res_vec.push('0');
    } else {
        while n > 0
        {
            if n % 2 == 1 {
                res_vec.push('1');
            } else {
                res_vec.push('0');
            }
            n = n / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Fixed type conversion issues and compilation errors */
{
    let x_val: u64 = Str2Int(sx@) as u64;
    let y_val: u64 = Str2Int(sy@) as u64;
    let z_val: u64 = Str2Int(sz@) as u64;
    let mut result: u64 = 1;
    let mut base: u64 = (x_val % z_val);
    let mut exp: u64 = y_val;
    
    while exp > 0
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    u64_to_bitvec(result)
}
// </vc-code>

fn main() {}
}
