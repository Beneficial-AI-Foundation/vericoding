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
/* helper modified by LLM (iteration 3): fixed return type from integer to int */
fn compare_vec(a: &Vec<char>, b: &Vec<char>) -> int {
    if a.len() > b.len() {
        1
    } else if a.len() < b.len() {
        -1
    } else {
        for i in 0..a.len() {
            if a[i] != b[i] {
                if a[i] == '1' {
                    return 1;
                } else {
                    return -1;
                }
            }
        }
        0
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
{
    /* code modified by LLM (iteration 3): fixed integer literals to avoid int type in executable code */
    if is_zero(&sy) {
        vec!['1']
    } else {
        let mut base = sx;
        base = mod_vec(base, sz.clone());
        let mut result = base;
        let mut i = 0;
        while i < n
            invariant
                i <= n,
            decreases n - i
        {
            result = square_vec(result);
            result = mod_vec(result, sz.clone());
            i = i + 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}