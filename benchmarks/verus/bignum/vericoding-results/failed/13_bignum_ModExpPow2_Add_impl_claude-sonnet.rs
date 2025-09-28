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
/* helper modified by LLM (iteration 10): accessing ghost type using get() method for accessing sequence elements */
fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
    requires valid_bit_string(s)
    ensures result@ == s && valid_bit_string(result@)
{
    let mut vec = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            vec@.len() == i as int,
            vec@ == s.subrange(0, i as int),
            valid_bit_string(vec@)
        decreases s.len() - i as int
    {
        vec.push(s.index(i as int));
        i = i + 1;
    }
    vec
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
    /* code modified by LLM (iteration 10): using index() method instead of bracket notation for sequence access */
    if n == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 0 || sy[n as usize] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut half_y_vec = Vec::new();
    
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            half_y_vec@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> half_y_vec@[j] == sy@[j],
            valid_bit_string(half_y_vec@)
        decreases n as int - i as int
    {
        half_y_vec.push(sy[i]);
        i = i + 1;
    }
    
    let half_result = mod_exp_pow2(sx.clone(), half_y_vec, n - 1, sz.clone());
    
    let squared = add(half_result@, half_result@);
    
    let squared_vec = seq_to_vec(squared);
    
    squared_vec
}
// </vc-code>


}

fn main() {}