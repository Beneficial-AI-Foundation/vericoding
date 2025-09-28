// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): fixed type issues in seq_to_vec helper */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            0 <= i <= s.len() as usize,
            v@ == s.subrange(0, i as int)
        decreases s.len() as usize - i
    {
        v.push(s[i as int]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): fixed type conversions and loop logic */
{
    let mut q = Vec::new();
    
    let n = dividend.len() as int;
    let d = divisor@;
    
    let mut current_r: Seq<char> = dividend@;
    
    let mut i: int = 0;
    while i < n
        invariant
            valid_bit_string(q@),
            valid_bit_string(current_r),
            str2int(dividend@) == str2int(divisor@) * str2int(q@) + str2int(current_r),
            str2int(current_r) < str2int(divisor@)
        decreases n - i
    {
        if str2int(current_r) >= str2int(d) {
            let new_r = sub(current_r, d);
            current_r = new_r;
            q.push('1');
        } else {
            q.push('0');
        }
        i += 1;
    }
    
    let result_r = seq_to_vec(current_r);
    (q, result_r)
}
// </vc-code>


}

fn main() {}