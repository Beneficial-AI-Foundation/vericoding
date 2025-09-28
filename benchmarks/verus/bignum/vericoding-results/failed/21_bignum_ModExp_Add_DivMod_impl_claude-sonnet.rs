// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed seq_to_vec to properly index sequences and nat comparisons */
spec fn vec_to_seq<T>(v: Vec<T>) -> Seq<T> {
    v@
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures res@ == s && valid_bit_string(res@)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i as int,
            result@ == s.subrange(0, i as int),
            valid_bit_string(result@)
    {
        let ghost idx = i as int;
        result.push(s[idx]);
        i = i + 1;
    }
    result
}

proof fn str2_int_empty()
    ensures str2_int(seq![]) == 0
{
}

proof fn str2_int_single_zero()
    ensures str2_int(seq!['0']) == 0
{
}

proof fn str2_int_single_one()
    ensures str2_int(seq!['1']) == 1
{
}

proof fn exp_int_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn exp_int_one(x: nat)
    ensures exp_int(x, 1) == x
{
}

fn bit_string_zero() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2_int(res@) == 0
{
    vec!['0']
}

fn bit_string_one() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2_int(res@) == 1
{
    vec!['1']
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed nat comparisons using 0nat and 1nat literals */
    if sy.len() == 0 {
        return bit_string_one();
    }
    
    if str2_int(sy@) == 0nat {
        return bit_string_one();
    }
    
    if str2_int(sx@) == 0nat {
        return bit_string_zero();
    }
    
    if str2_int(sx@) == 1nat {
        return bit_string_one();
    }
    
    let last_bit = sy[sy.len() - 1];
    let ghost sy_prefix = sy@.subrange(0, sy@.len() - 1);
    let sy_prefix_vec = seq_to_vec(sy_prefix);
    
    let half_result = mod_exp(sx.clone(), sy_prefix_vec, sz.clone());
    let squared = add(half_result@, half_result@);
    let (_, squared_mod) = div_mod(squared, sz@);
    
    if last_bit == '0' {
        seq_to_vec(squared_mod)
    } else {
        let temp = add(squared_mod, sx@);
        let (_, final_mod) = div_mod(temp, sz@);
        seq_to_vec(final_mod)
    }
}
// </vc-code>


}

fn main() {}