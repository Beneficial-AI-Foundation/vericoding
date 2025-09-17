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
/* helper modified by LLM (iteration 2): Fix type mismatches in lemmas by using nat instead of int parameters */
proof fn lemma_exp_mul_mod(x: nat, y: nat, z: nat)
    requires
        z > 1,
        y > 0,
    ensures
        (Exp_int(x, y) % z) == (((x % z) * Exp_int(x, y - 1)) % z)
{
}

proof fn lemma_exp_base(x: nat)
    ensures
        Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_recursive(x: nat, y: nat)
    requires
        y > 0,
    ensures
        Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

proof fn lemma_mod_properties(x: nat, y: nat, z: nat)
    requires
        z > 1,
    ensures
        (x * y) % z == ((x % z) * y) % z
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix type conversion issues and native integer operations */
{
    let sy_int = Str2Int(sy@);
    let sz_int = Str2Int(sz@);
    let sx_int = Str2Int(sx@);
    
    if sy_int == 0 {
        return "1".chars().collect();
    } else if sy_int == 1 {
        let x_mod_z = sx_int % sz_int;
        return format!("{}", x_mod_z).chars().collect();
    } else {
        let half_sy = sy_int / 2;
        let half_sy_str = format!("{:b}", half_sy).chars().collect::<Vec<char>>();
        let recursive_result = ModExp_Mul_Zeroes(sx, &half_sy_str, sz);
        let temp = Str2Int(recursive_result@);
        let square_mod = (temp * temp) % sz_int;
        
        if sy_int % 2 == 1 {
            let result = (square_mod * (sx_int % sz_int)) % sz_int;
            return format!("{}", result).chars().collect();
        } else {
            return format!("{}", square_mod).chars().collect();
        }
    }
}
// </vc-code>

fn main() {}
}
