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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0
  ensures 
    ({
       let (quotient, remainder) = result; 
       valid_bit_string(quotient) && valid_bit_string(remainder) &&
       str2int(quotient) == str2int(dividend) / str2int(divisor) &&
       str2int(remainder) == str2int(dividend) % str2int(divisor)
    })
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
proof fn seq_concat(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
    ensures res == s1 + s2 && valid_bit_string(res)
{
    s1 + s2
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fix seq_concat usage and while loop with proper sequence operations */
    let sy_len = sy.len();
    let sz_seq = sz@;
    let sx_seq = sx@;
    let sy_seq = sy@;
    
    let mut result_seq = sx_seq;
    let mut remaining_len = sy_len;
    let mut target_power = seq_concat(sy_seq, seq![]);
    
    while remaining_len > 0
        invariant
            valid_bit_string(result_seq),
            str2int(result_seq) == exp_int(str2int(sx_seq), str2int(target_power.subrange(0, remaining_len as int))) % str2int(sz_seq),
            remaining_len <= sy_len
        decreases remaining_len
    {
        let bit_pos = (remaining_len - 1) as nat;
        let current_sy = target_power.subrange(0, remaining_len as int);
        
        let next_power = mod_exp_pow2_recursive(result_seq, current_sy, remaining_len, sz_seq);
        result_seq = next_power;
        remaining_len = remaining_len - 1;
    }
    
    let mut res_vec = Vec::with_capacity(result_seq.len() as usize);
    for i in 0..result_seq.len() {
        res_vec.push(result_seq[i]);
    }
    res_vec
}
// </vc-code>


}

fn main() {}