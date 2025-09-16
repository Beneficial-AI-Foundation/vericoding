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
/* helper modified by LLM (iteration 10): Fix nat literal syntax and remove unnecessary type annotations */
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

spec fn nat_div(a: nat, b: nat) -> nat
    requires b > 0
{
    (a / b) as nat
}

spec fn nat_mod(a: nat, b: nat) -> nat
    requires b > 0
{
    (a % b) as nat
}

spec fn nat_eq(a: nat, b: nat) -> bool
{
    a == b
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix nat literal syntax and use proper type conversions */
{
    let sy_nat = Str2Int(sy@);
    let sz_nat = Str2Int(sz@);
    let sx_nat = Str2Int(sx@);
    
    if sy_nat == 0 {
        return vec!['1'];
    } else if sy_nat == 1 {
        let x_mod_z = sx_nat % sz_nat;
        if x_mod_z == 0 {
            return vec!['0'];
        } else {
            let mut result = Vec::new();
            let mut temp = x_mod_z;
            while temp > 0 {
                if temp % 2 == 1 {
                    result.insert(0, '1');
                } else {
                    result.insert(0, '0');
                }
                temp = temp / 2;
            }
            return result;
        }
    } else {
        let half_sy = sy_nat / 2;
        let half_sy_vec = if half_sy == 0 { vec!['0'] } else {
            let mut temp = half_sy;
            let mut result = Vec::new();
            while temp > 0 {
                if temp % 2 == 1 {
                    result.insert(0, '1');
                } else {
                    result.insert(0, '0');
                }
                temp = temp / 2;
            }
            result
        };
        let recursive_result = ModExp_Mul_Zeroes(sx, &half_sy_vec, sz);
        let temp = Str2Int(recursive_result@);
        let square_mod = (temp * temp) % sz_nat;
        
        if sy_nat % 2 == 1 {
            let result_val = (square_mod * (sx_nat % sz_nat)) % sz_nat;
            if result_val == 0 {
                return vec!['0'];
            } else {
                let mut temp = result_val;
                let mut result_vec = Vec::new();
                while temp > 0 {
                    if temp % 2 == 1 {
                        result_vec.insert(0, '1');
                    } else {
                        result_vec.insert(0, '0');
                    }
                    temp = temp / 2;
                }
                return result_vec;
            }
        } else {
            if square_mod == 0 {
                return vec!['0'];
            } else {
                let mut temp = square_mod;
                let mut result_vec = Vec::new();
                while temp > 0 {
                    if temp % 2 == 1 {
                        result_vec.insert(0, '1');
                    } else {
                        result_vec.insert(0, '0');
                    }
                    temp = temp / 2;
                }
                return result_vec;
            }
        }
    }
}
// </vc-code>

fn main() {}
}
