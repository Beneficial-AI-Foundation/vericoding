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
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) + str2int(s2)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed unused helper comment */
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
/* code modified by LLM (iteration 10): Fixed type mismatch in comparison with `str2int(sy@)` by casting it to `int`. */
{
    let zero_char_vec = vec!['0'];
    if str2int(sy@) as int == 0 {
        let mut one = Vec::new();
        one.push('1');
        return one;
    }

    if n == 0 {
        zero_char_vec
    } else {
        let n_minus_1_val: u8 = n - 1;
        proof {
            assert(n > 0 ==> n_minus_1_val < n);
            assert(n > 0 ==> n_minus_1_val >= 0);
        }

        let mut sy_half_vec: Vec<char> = Vec::new();
        sy_half_vec.push('1');
        for _i in 0..n_minus_1_val {
            sy_half_vec.push('0');
        }

        let res_half = mod_exp_pow2(sx.clone(), sy_half_vec.clone(), n - 1, sz.clone());
        
        zero_char_vec
    }
}
// </vc-code>


}

fn main() {}