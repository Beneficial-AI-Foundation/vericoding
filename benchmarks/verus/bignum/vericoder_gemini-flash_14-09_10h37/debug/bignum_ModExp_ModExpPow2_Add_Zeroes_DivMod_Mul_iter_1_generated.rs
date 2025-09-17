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
spec fn exp_mod(base: nat, exp: nat, modulus: nat) -> nat {
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = exp / 2;
        let res = exp_mod(base, half_exp, modulus);
        (res * res) % modulus
    } else {
        (base * exp_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
        let x = Str2Int(sx@);
        let y = Str2Int(sy@);
        let z = Str2Int(sz@);

        let result_nat = exp_mod(x, y, z);
        
        // Convert the nat result to a binary string (Seq<char>) and then to Vec<char>
        let mut result_seq = Seq::<char>::new();
        let mut temp_val = result_nat;
        if temp_val == 0 {
            result_seq = Seq::singleton('0');
        } else {
            while temp_val > 0 {
                let digit = if temp_val % 2 == 0 { '0' } else { '1' };
                result_seq = Seq::new(1, |i| digit).add(result_seq);
                temp_val = temp_val / 2;
            }
        }

        let mut res_vec = Vec::<char>::new();
        let mut i = 0;
        while i < result_seq.len()
            invariant
                res_vec.len() == i,
                forall |j: int| 0 <= j && j < i ==> res_vec.index(j) == result_seq.index(j)
        {
            res_vec.push(result_seq.index(i));
            i = i + 1;
        }
        res_vec
    }
// </vc-code>

fn main() {}
}
