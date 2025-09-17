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

spec fn Exp_int_mod(x: nat, y: nat, m: nat) -> nat
decreases y
{
    if y == 0 {
        1 % m
    } else {
        (x % m) * Exp_int_mod(x, (y - 1) as nat, m) % m
    }
}

proof fn exp_int_mod_proof(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int_mod(x, y, m)
    decreases y
{
    if y > 0 {
        exp_int_mod_proof(x, (y - 1) as nat, m);
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        exp_int_mod_proof(x_val, y_val, z_val);
    }
    
    let result_val = Exp_int_mod(x_val, y_val, z_val);
    let mut result_bits = Vec::<char>::new();
    let mut val = result_val;
    
    while val > 0
        invariant
            val >= 0,
            ValidBitString(Seq::from_vec(result_bits@)),
            Str2Int(Seq::from_vec(result_bits@)) == result_val - val * Exp_int(2, result_bits@.len() as nat)
        decreases val
    {
        let bit_char = if val % 2 == 1 { '1' } else { '0' };
        result_bits.push(bit_char);
        val = val / 2;
    }
    
    result_bits.reverse();
    result_bits
}
// </vc-code>

fn main() {}
}
