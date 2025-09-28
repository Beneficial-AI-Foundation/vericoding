// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type conversion and result variable handling */
fn seq_to_vec(s: Seq<char>) -> Vec<char>
    ensures
        result@ == s,
        valid_bit_string(result@)
{
    let mut v = Vec::new();
    let len: usize = s.len() as usize;
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            v@ == s.subrange(0, i as int)
    {
        v.push(s[i as int]);
        i = i + 1;
    }
    v
}

fn vec_to_seq(v: Vec<char>) -> Seq<char>
    ensures
        result == v@
{
    v@
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
{
    /* code modified by LLM (iteration 10): Fixed result variable handling and proper initialization */
    let mut result_vec = Vec::new();
    result_vec.push('1');
    let mut base = sx;
    let exp_len = sy.len();
    let mut exp_index: usize = exp_len;
    let mod_val = sz;
    
    while exp_index > 0
        invariant
            valid_bit_string(result_vec@),
            valid_bit_string(base@),
            exp_index <= exp_len,
            exp_index >= 0
        decreases exp_index
    {
        let current_char = sy[exp_index - 1];
        if current_char == '1' {
            let temp_result_seq = mul(result_vec@, base@);
            let temp_res_seq = mod_exp_pow2(temp_result_seq, seq!['1'], 0, mod_val@);
            result_vec = seq_to_vec(temp_res_seq);
        }
        
        let squared_base_seq = mul(base@, base@);
        let base_res_seq = mod_exp_pow2(squared_base_seq, seq!['1'], 0, mod_val@);
        base = seq_to_vec(base_res_seq);
        
        exp_index = exp_index - 1;
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}