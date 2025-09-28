// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
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
/* helper modified by LLM (iteration 10): Fix type errors and remove spec types from executable code */
fn seq_to_vec(s: Seq<char>) -> Vec<char> {
    let mut v = Vec::new();
    let mut i: usize = 0;
    let len: usize = s.len() as usize;
    while i < len
        invariant
            0 <= i <= len,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j],
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

proof fn lemma_exp_int_zero(x: nat) 
    ensures exp_int(x, 0nat) == 1nat,
{
}

proof fn lemma_mod_exp_pow2_base_case(x: nat, z: nat) 
    requires z > 1,
    ensures exp_int(x, 0nat) % z == 1nat % z,
{
}

proof fn lemma_mod_exp_pow2_recursive(x: nat, n: nat, z: nat) 
    requires z > 1,
    ensures exp_int(x, exp_int(2nat, n)) % z == exp_int(exp_int(x, exp_int(2nat, (n - 1nat) as nat)) % z, 2nat) % z,
{
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
    decreases n as nat
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fix type conversion and implement proper logic */
    if str2int(sy@) == 0 {
        // Base case: x^0 % z = 1 % z
        let mut one = Vec::new();
        one.push('1');
        one
    } else if n == 0 {
        // Base case for n=0
        let mut one = Vec::new();
        one.push('1');
        one
    } else {
        // Recursive case
        let new_n = n - 1;
        let mut new_sy = Vec::new();
        for i in 0..(new_n as usize + 1) {
            if i == 0 { 
                new_sy.push('1'); 
            } else { 
                new_sy.push('0'); 
            }
        }
        let x_mod_z = mod_exp_pow2(sx.clone(), new_sy, new_n, sz.clone());
        let x_sq = mul(x_mod_z@, x_mod_z@);
        let x_sq_vec = seq_to_vec(x_sq);
        x_sq_vec
    }
}
// </vc-code>


}

fn main() {}