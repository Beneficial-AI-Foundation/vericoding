// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == 49u8 { 1nat } else { 0nat })
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
/* helper modified by LLM (iteration 10): Convert Seq to Vec for executable code */
fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ =~= s
{
    let mut vec_result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            vec_result.len() == i,
            forall|j: int| 0 <= j < i ==> vec_result@[j] == s[j],
    {
        vec_result.push(s[i as int]);
        i = i + 1;
    }
    vec_result
}

/* helper modified by LLM (iteration 10): Wrapper for add function */
fn add_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == str2int(s1@) + str2int(s2@)
{
    let seq_result = add(s1@, s2@);
    seq_to_vec(seq_result)
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
    /* code modified by LLM (iteration 10): Keep same recursive logic */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut result = Vec::new();
            result.push('1');
            proof {
                assert(sy@.len() == 1);
                assert(sy@[0] == '0');
                assert(str2int(sy@) == 0nat);
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
                assert(result@.len() == 1);
                assert(result@[0] == '1');
                assert(str2int(result@) == 1nat);
                assert(1nat % str2int(sz@) < str2int(sz@));
            }
            result
        } else {
            let mut result = sx.clone();
            proof {
                assert(sy@.len() == 1);
                assert(sy@[0] == '1');
                assert(str2int(sy@) == 1nat);
                assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
                assert(result@ =~= sx@);
            }
            result
        }
    } else {
        let last_bit = sy[sy.len() - 1];
        let mut sy_half = Vec::new();
        for i in 0..sy.len() - 1
            invariant
                sy_half.len() == i,
                forall|j: int| 0 <= j < i ==> sy_half@[j] == sy@[j],
        {
            sy_half.push(sy[i]);
        }
        
        let temp = mod_exp(sx.clone(), sy_half, sz.clone());
        let temp_squared = mod_exp(temp.clone(), temp.clone(), sz.clone());
        
        if last_bit == '0' {
            temp_squared
        } else {
            let result = add_vec(temp_squared, sx.clone());
            result
        }
    }
}
// </vc-code>


}

fn main() {}