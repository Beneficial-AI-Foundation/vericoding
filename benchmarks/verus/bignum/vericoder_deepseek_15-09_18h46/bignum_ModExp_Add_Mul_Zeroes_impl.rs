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
/* helper modified by LLM (iteration 10): fixed type conversion and added mod_exp_recursive helper */
spec fn mod_exp_recursive(base: nat, exponent: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exponent
{
    if exponent == 0 {
        1
    } else {
        let half_exp = mod_exp_recursive(base, exponent / 2, modulus);
        let temp = (half_exp * half_exp) % modulus;
        if exponent % 2 == 0 {
            temp
        } else {
            (temp * base) % modulus
        }
    }
}

/* helper modified by LLM (iteration 10): fixed type conversion in seq_to_vec */
fn seq_to_vec(s: Seq<char>) -> Vec<char>
    ensures result@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            0 <= i && i <= s.len() as usize,
            v@ == s.subrange(0, i as int)
        decreases s.len() as usize - i
    {
        v.push(s[i]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): fixed variable handling and result declaration */
{
    let base_val = Str2Int(sx@);
    let exponent_val = Str2Int(sy@);
    let modulus_val = Str2Int(sz@);
    
    let result_num = mod_exp_recursive(base_val, exponent_val, modulus_val);
    
    let binary_result = num_to_binary_spec(result_num);
    
    let result = seq_to_vec(binary_result);
    result
}
// </vc-code>

fn main() {}
}
