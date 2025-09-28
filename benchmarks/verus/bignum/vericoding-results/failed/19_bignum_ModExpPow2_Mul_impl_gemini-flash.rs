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
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed compilation error as `lemma` functions are not allowed to be `fn` */
lemma fn pow2_minus_one_is_divisible_by_two_minus_one(k: nat)
    ensures (exp_int(2, k) - 1) % (2 - 1) == 0
{
    if k == 0 {
        // Base case: 2^0 - 1 = 0, which is divisible by 1
    } else {
        let k_minus_1 = (k - 1) as nat;
        pow2_minus_one_is_divisible_by_two_minus_one(k_minus_1);
        // 2^k - 1 = 2 * (2^(k-1) - 1) + 1
        assert((exp_int(2, k) - 1) % 1 == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
        sy@.len() == n as int + 1 &&
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed the error where pow_minus_one_is_divisible_by_two_minus_one accepts `k: nat` */
{
    // Base case: n == 0
    if n == 0 {
        proof {
            if str2int(sy@) == 0nat {
                assert(exp_int(str2int(sx@), 0nat) % str2int(sz@) == 1nat % str2int(sz@));
            } else {
                assert(str2int(sy@) == 1nat) by { assert(exp_int(2nat, 0nat) == 1nat); };
                assert(exp_int(str2int(sx@), 1nat) % str2int(sz@) == str2int(sx@) % str2int(sz@));
            }
        }
        let res_nat: nat = if str2int(sy@) == 0nat { 1nat % str2int(sz@) } else { str2int(sx@) % str2int(sz@) };
        let sz_nat = str2int(sz@);
        let len_for_int2str: usize = if sz_nat == 1 { 1 } else { (log2_ceil(sz_nat)) as usize };

        return int2str(Ghost(res_nat), len_for_int2str);
    }

    // Recursive step
    let half_sy_nat: nat = str2int(sy@) / 2nat;

    let k_usize = (n as nat).max(1) as usize; // Ensure k_usize is at least 1

    let half_sy_vec = int2str(Ghost(half_sy_nat), k_usize);
    let half_sy_seq = half_sy_vec@;

    let rem_exp_x_half_sy_vec = mod_exp_pow2(sx, half_sy_vec, (n - 1) as u8, sz);
    let rem_exp_x_half_sy = str2int(rem_exp_x_half_sy_vec@);

    let final_res_nat: nat = if str2int(sy@) % 2nat == 1nat {
        let sx_nat = str2int(sx@);
        let sz_nat = str2int(sz@);

        let term1 = (rem_exp_x_half_sy * rem_exp_x_half_sy) % sz_nat;
        (term1 * (sx_nat % sz_nat)) % sz_nat
    } else {
        let sz_nat = str2int(sz@);
        (rem_exp_x_half_sy * rem_exp_x_half_sy) % sz_nat
    };

    proof {
        assert(final_res_nat == mod_spec_exp_pow2_helper(sx@, sy@, n as nat, sz@));
        sz@.len() >= 1;
        // sz_nat > 1;
        if str2int(sz@) > 1 {
            pow2_minus_one_is_divisible_by_two_minus_one((log2_ceil(str2int(sz@))));
        }
        
    }
    let sz_nat = str2int(sz@);
    let len_for_int2str: usize = if sz_nat == 1 { 1 } else { (log2_ceil(sz_nat)) as usize };

    int2str(Ghost(final_res_nat), len_for_int2str)
}
// </vc-code>


}

fn main() {}