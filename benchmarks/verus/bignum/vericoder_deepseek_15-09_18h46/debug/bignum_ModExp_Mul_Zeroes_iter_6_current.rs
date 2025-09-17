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
/* helper modified by LLM (iteration 6): Fix nat literal syntax and add proper conversion helpers */
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

spec fn nat_to_usize(n: nat) -> usize
{
    n as usize
}

spec fn nat_sub(a: nat, b: nat) -> nat
    requires a >= b
{
    (a - b) as nat
}

spec fn nat_zero() -> nat { 0 }
spec fn nat_one() -> nat { 1 }
spec fn nat_two() -> nat { 2 }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Fix nat literal syntax and conversion issues */
{
    let sy_nat = Str2Int(sy@);
    let sz_nat = Str2Int(sz@);
    let sx_nat = Str2Int(sx@);
    
    if sy_nat == 0 {
        return "1".chars().collect();
    } else if sy_nat == 1 {
        let x_mod_z = sx_nat % sz_nat;
        return x_mod_z.to_string().chars().collect();
    } else {
        let half_sy = sy_nat / 2;
        let half_sy_str = half_sy.to_string().chars().collect::<Vec<char>>();
        let recursive_result = ModExp_Mul_Zeroes(sx, &half_sy_str, sz);
        let temp = Str2Int(recursive_result@);
        let square_mod = (temp * temp) % sz_nat;
        
        if sy_nat % 2 == 1 {
            let result = (square_mod * (sx_nat % sz_nat)) % sz_nat;
            return result.to_string().chars().collect();
        } else {
            return square_mod.to_string().chars().collect();
        }
    }
}
// </vc-code>

fn main() {}
}
