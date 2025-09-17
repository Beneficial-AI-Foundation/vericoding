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
/* helper modified by LLM (iteration 5): Fixed nat operations with proper type casting */
fn is_even(n: nat) -> bool
    ensures is_even(n) == (n % 2 == 0)
{
    (n % 2) == 0
}

fn div_by_2(n: nat) -> nat
    ensures div_by_2(n) == n / 2
{
    n / 2
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed nat type annotations and loop invariants */
{
    let x_val = Str2Int(sx@);
    let mut y_val: nat = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    let mut result: nat = 1;
    let mut base: nat = x_val % z_val;
    
    while y_val > 0
        invariant
            result == Exp_int(x_val, y_val) % z_val,
            base == (x_val % z_val) * Exp_int(base, 1) % z_val,
        decreases y_val
    {
        if !is_even(y_val) {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        y_val = div_by_2(y_val);
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut temp: nat = result;
    
    while temp > 0
        invariant
            temp >= 0,
        decreases temp
    {
        if !is_even(temp) {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = div_by_2(temp);
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
