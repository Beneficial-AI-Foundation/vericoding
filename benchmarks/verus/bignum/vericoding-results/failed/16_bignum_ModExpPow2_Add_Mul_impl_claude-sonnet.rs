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
/* helper modified by LLM (iteration 10): conversion helper using only executable types to avoid ghost indexing errors */
fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
    requires valid_bit_string(s)
    ensures 
        result@.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> result@[i] == s[i],
        valid_bit_string(result@)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let s_len = s.len();
    
    while i < s_len as usize
        invariant
            0 <= i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s[j],
            valid_bit_string(result@)
    {
        result.push(s[i as int]);
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 10): fixed indexing to use Vec methods instead of Seq indexing */
    if n == 0 {
        if sy[0] == '1' {
            let one = vec!['1'];
            return one;
        } else {
            let zero = vec!['0'];
            return zero;
        }
    }
    
    let sy_half = sy.clone();
    let mut sy_half_vec = sy_half;
    sy_half_vec.truncate((n) as usize);
    
    let rec_result = mod_exp_pow2(sx.clone(), sy_half_vec, n - 1, sz.clone());
    
    let squared = mul(rec_result@, rec_result@);
    let squared_vec = seq_to_vec(squared);
    
    if sy[0] == '1' {
        let temp = mul(squared, sx@);
        let temp_vec = seq_to_vec(temp);
        return temp_vec;
    } else {
        return squared_vec;
    }
}
// </vc-code>


}

fn main() {}