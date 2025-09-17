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
/* helper modified by LLM (iteration 5): Added vec_from_nat function */
fn vec_from_nat(n: nat) -> (v: Vec<char>)
    ensures ValidBitString(v@), Str2Int(v@) == n
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
    } else {
        while num > 0
            invariant
                ValidBitString(result@),
                num + Str2Int(result@) == n,
                num >= 0
            decreases num
        {
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
        }
        result.reverse();
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using proper vec_from_nat function */
{
    let z_int = Str2Int(sz@);
    let mut x_int: nat = Str2Int(sx@);
    let mut y_int: nat = Str2Int(sy@);
    let mut result_int: nat = 1;
    
    proof {
        str2int_nonnegative(sy@);
        exp_int_nonnegative(Str2Int(sx@), y_int);
    }
    
    while y_int > 0
        invariant
            result_int == Exp_int(Str2Int(sx@), y_int) % z_int,
            0 <= y_int <= Str2Int(sy@)
        decreases y_int
    {
        if y_int % 2 == 1 {
            result_int = (result_int * x_int) % z_int;
        }
        
        x_int = (x_int * x_int) % z_int;
        y_int = y_int / 2;
        
        proof { mod_exp_lemmas(); }
    }
    
    let res = vec_from_nat(result_int);
    res
}
// </vc-code>

fn main() {}
}
