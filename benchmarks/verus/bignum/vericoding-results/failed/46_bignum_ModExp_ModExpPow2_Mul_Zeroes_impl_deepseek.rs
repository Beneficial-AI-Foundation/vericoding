// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
        sy.len() == n + 1,
        str2int(sz) > 1
    ensures 
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases n
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
    ensures 
        s.len() == n,
        valid_bit_string(s),
        str2int(s) == 0,
        all_zero(s)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed nat literals and seq conversion */
fn bit_at(vec: Vec<char>, index: usize) -> char
    requires 0 <= index < vec.len()
{
    vec[index]
}

fn is_odd_char(c: char) -> bool {
    c == '1'
}

fn update_result(result: &mut Vec<char>, base: &Vec<char>, sz: &Vec<char>) 
    requires 
        valid_bit_string(result@) && valid_bit_string(base@) && valid_bit_string(sz@),
        str2int(sz@) > 1
{
    let temp_res = mul(result@, base@);
    *result = mod_exp_pow2(temp_res, zeros(0), 0, sz@).to_vec_owned();
}

fn square_vec(vec: &mut Vec<char>, sz: &Vec<char>) 
    requires 
        valid_bit_string(vec@) && valid_bit_string(sz@),
        str2int(sz@) > 1
{
    let temp = mul(vec@, vec@);
    *vec = mod_exp_pow2(temp, zeros(0), 0, sz@).to_vec_owned();
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        sy.len() > 0 && str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed nat literals and seq conversion */
{
    let mut result = Vec::new();
    result.push('1');
    let mut base = sx.clone();
    
    let len = sy.len();
    let mut i = (len - 1) as i64;
    
    while i >= 0
        invariant
            valid_bit_string(result@) && valid_bit_string(base@),
            str2int(result@) == exp_int(str2int(sx@), str2int(sy@.subrange(i as int + 1, len as int))) % str2int(sz@),
            str2int(base@) == exp_int(str2int(sx@), exp_int(2, (len - 1 - i as usize) as nat)) % str2int(sz@),
            i >= -1
        decreases i + 1
    {
        let idx = i as usize;
        let bit = bit_at(sy.clone(), idx);
        
        if is_odd_char(bit) {
            update_result(&mut result, &base, &sz);
        }
        
        if i > 0 {
            square_vec(&mut base, &sz);
        }
        
        i = i - 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}