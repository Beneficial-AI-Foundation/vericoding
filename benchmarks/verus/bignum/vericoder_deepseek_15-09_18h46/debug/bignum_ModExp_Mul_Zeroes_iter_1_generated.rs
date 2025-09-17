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

proof fn lemma_exp_mul_mod(x: int, y: int, z: int)
    requires
        x >= 0,
        y >= 0,
        z > 1,
    ensures
        (Exp_int(x, y) % z) == (((x % z) * Exp_int(x, y - 1)) % z)
{
}

proof fn lemma_exp_base(x: int, y: int)
    requires
        x >= 0,
        y == 0,
    ensures
        Exp_int(x, y) == 1
{
}

proof fn lemma_exp_recursive(x: int, y: int)
    requires
        x >= 0,
        y > 0,
    ensures
        Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

proof fn lemma_mod_properties(x: int, y: int, z: int)
    requires
        x >= 0,
        y >= 0,
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
{
    if sy.len() == 1 {
        if sy[0] == '1' {
            let x_mod_z = Str2Int(sx@) % Str2Int(sz@);
            return x_mod_z.to_string().chars().collect();
        } else {
            return "1".chars().collect();
        }
    } else {
        let half_sy = &sy[0..sy.len() - 1];
        let recursive_result = ModExp_Mul_Zeroes(sx, half_sy, sz);
        let temp = Str2Int(recursive_result@);
        let square_mod = (temp * temp) % Str2Int(sz@);
        if sy[sy.len() - 1] == '1' {
            let result = (square_mod * (Str2Int(sx@) % Str2Int(sz@))) % Str2Int(sz@);
            return result.to_string().chars().collect();
        } else {
            return square_mod.to_string().chars().collect();
        }
    }
}
// </vc-code>

fn main() {}
}
