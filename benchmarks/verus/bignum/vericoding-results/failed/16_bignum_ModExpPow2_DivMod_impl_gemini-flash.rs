// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
    ensures 
        valid_bit_string(result.0) && valid_bit_string(result.1),
        str2int(result.0) == str2int(dividend) / str2int(divisor),
        str2int(result.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatches by casting '2' to `nat` where division and modulus operations are involved with `nat` types. Changed signature to spec fn since this is meant to be a specification helper. */
spec fn mod_exp_pow2_helper(x: nat, n_bits: u8, z_val: nat) -> nat
    requires
        z_val > 1
    ensures
        mod_exp_pow2_helper(x, n_bits, z_val) == exp_int(x, exp_int(2, n_bits as nat)) % z_val
    decreases n_bits
{
    if n_bits == 0 {
        x % z_val
    } else {
        let res_half = mod_exp_pow2_helper(x, (n_bits - 1) as u8, z_val);
        (res_half * res_half) % z_val
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy.len() == n as int + 1,
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type mismatches by casting literals to `nat` to match other `nat` types where modulus, comparisons, and division are involved. */
{
    let x_val = str2int(sx@);
    let y_val = str2int(sy@);
    let z_val = str2int(sz@);

    let result_nat: nat = if y_val == 0 {
        1nat % z_val
    } else {
        mod_exp_pow2_helper(x_val, n, z_val)
    };

    let mut final_res_vec: Vec<char> = Vec::new();
    if result_nat == 0 {
        final_res_vec.push('0');
    } else {
        let mut temp_val = result_nat;
        while temp_val > 0nat
            invariant
                temp_val >= 0,
            decreases temp_val
        {
            let digit = temp_val % 2nat;
            if digit == 1nat {
                final_res_vec.push('1');
            } else {
                final_res_vec.push('0');
            }
            temp_val = temp_val / 2nat;
        }
        final_res_vec.reverse(); // To get the correct bit order
    }
    final_res_vec
}
// </vc-code>


}

fn main() {}