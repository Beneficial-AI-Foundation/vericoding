// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1) &&
    str2int(ret.0) == str2int(dividend) / str2int(divisor) &&
    str2int(ret.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed compilation error by using usize index instead of int cast */
spec fn is_zero(s: Seq<char>) -> bool
{
  s.len() == 0 || (s.len() == 1 && s[0] == '0')
}

spec fn is_one(s: Seq<char>) -> bool
{
  s.len() == 1 && s[0] == '1'
}

spec fn is_even(s: Seq<char>) -> bool
  requires s.len() > 0
{
  s[s.len() - 1] == '0'
}

fn right_shift(s: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s), s.len() > 0
  ensures valid_bit_string(res),
          str2int(res) == str2int(s) / 2
{
  if s.len() == 1 {
    seq!['0']
  } else {
    s.subrange(0, s.len() - 1)
  }
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
  requires valid_bit_string(s)
  ensures res@ == s, valid_bit_string(res@)
{
  let mut result_vec = Vec::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      result_vec@.len() == i,
      result_vec@ == s.subrange(0, i as int)
  {
    result_vec.push(s[i]);
    i = i + 1;
  }
  result_vec
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): fixed compilation error by using usize index instead of int cast */
  let zero = seq!['0'];
  let one = seq!['1'];
  
  let ghost sy_spec = sy@;
  let ghost sx_spec = sx@;
  let ghost sz_spec = sz@;
  
  if is_zero(sy_spec) {
    return vec!['1'];
  }
  
  if is_one(sy_spec) {
    let (_, remainder) = div_mod(sx_spec, sz_spec);
    return seq_to_vec(remainder);
  }
  
  let mut result = one;
  let mut base = sx_spec;
  let mut exp = sy_spec;
  
  while !is_zero(exp)
    invariant
      valid_bit_string(result),
      valid_bit_string(base),
      valid_bit_string(exp),
      str2int(sz_spec) > 1,
      str2int(result) * exp_int(str2int(base), str2int(exp)) % str2int(sz_spec) == exp_int(str2int(sx_spec), str2int(sy_spec)) % str2int(sz_spec)
    decreases str2int(exp)
  {
    if !is_even(exp) {
      result = mul(result, base);
      let (_, remainder) = div_mod(result, sz_spec);
      result = remainder;
    }
    
    base = mul(base, base);
    let (_, remainder) = div_mod(base, sz_spec);
    base = remainder;
    
    
    exp = right_shift(exp);
  }
  
  seq_to_vec(result)
}
// </vc-code>


}

fn main() {}