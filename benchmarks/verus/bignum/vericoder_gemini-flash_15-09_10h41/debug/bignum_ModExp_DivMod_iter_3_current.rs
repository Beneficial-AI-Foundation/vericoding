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
/* helper modified by LLM (iteration 3): No change as helper definitions are already correct. */
spec fn ModExp_DivMod_spec_internal(x_val: nat, y_val: nat, z_val: nat) -> nat
decreases y_val
{
    if y_val == 0 { 1nat % z_val }
    else if y_val % 2 == 0 {
        let half_pow = ModExp_DivMod_spec_internal(x_val, y_val / 2, z_val);
        (half_pow * half_pow) % z_val
    }
    else {
        let half_pow = ModExp_DivMod_spec_internal(x_val, (y_val - 1) / 2, z_val);
        (x_val * half_pow * half_pow) % z_val
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed the type issue with `nat` in the `int_to_bit_vec` helper function by using `n / 2` directly and explicitly asserting type `nat` for `remainder` and `num`. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    // Base case: y_val is 0, result is 1 % z
    if y_val == 0 {
        let res_val = 1nat % z_val;
        return int_to_bit_vec(res_val);
    }

    // Recursive step: Divide and Conquer
    if y_val % 2 == 0 { // y is even
        let mut vec_y_div_2: Vec<char> = Vec::new();
        let y_div_2: nat = y_val / 2;
        vec_y_div_2 = int_to_bit_vec(y_div_2);

        let half_pow_vec = ModExp_DivMod(sx, &*vec_y_div_2, sz);

        let half_pow_val = Str2Int(half_pow_vec@);
        let res_val = (half_pow_val * half_pow_val) % z_val;
        assert(res_val == ModExp_DivMod_spec_internal(x_val, y_val, z_val));
        return int_to_bit_vec(res_val);
    } else { // y is odd
        let mut vec_y_minus_1_div_2: Vec<char> = Vec::new();
        let y_minus_1_div_2: nat = (y_val - 1) / 2;
        vec_y_minus_1_div_2 = int_to_bit_vec(y_minus_1_div_2);

        let half_pow_vec = ModExp_DivMod(sx, &*vec_y_minus_1_div_2, sz);
        let half_pow_val = Str2Int(half_pow_vec@);
        let res_val = (x_val * half_pow_val * half_pow_val) % z_val;
        assert(res_val == ModExp_DivMod_spec_internal(x_val, y_val, z_val));
        return int_to_bit_vec(res_val);
    }

    fn int_to_bit_vec(n: nat) -> Vec<char> {
        if n == 0 { return vec!['0']; }
        let mut bits = Vec::new();
        let mut num: nat = n;
        while num > 0
        invariant
            num >= 0,
        {
            let remainder: nat = num % 2;
            bits.push(if remainder == 1 { '1' } else { '0' });
            num = num / 2;
        }
        bits.into_iter().rev().collect()
    }
}
// </vc-code>

fn main() {}
}
