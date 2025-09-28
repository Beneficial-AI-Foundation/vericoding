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
/* helper modified by LLM (iteration 10): fixed type mismatches by using usize instead of int for indexing */
fn find_highest_bit(s: &Vec<char>) -> (result: usize)
  requires valid_bit_string(s@) && s.len() > 0
  ensures result < s.len()
{
  let mut i = 0;
  while i < s.len()
    invariant i <= s.len()
  {
    if s[i] == '1' {
      return i;
    }
    i += 1;
  }
  s.len() - 1
}

fn create_power_of_two(n: usize) -> (result: Vec<char>)
  ensures 
    result.len() == n + 1,
    valid_bit_string(result@),
    str2int(result@) == exp_int(2nat, n as nat)
{
  let mut res = Vec::new();
  res.push('1');
  let mut i = 0;
  while i < n
    invariant 
      i <= n,
      res.len() == i + 1,
      valid_bit_string(res@)
  {
    res.push('0');
    i += 1;
  }
  res
}

fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
  requires valid_bit_string(s)
  ensures 
    result@ == s,
    valid_bit_string(result@)
{
  let mut result = Vec::new();
  let mut i = 0usize;
  while i < s.len() as usize
    invariant 
      i <= s.len() as usize,
      result.len() == i,
      result@ == s.subrange(0, i as int)
  {
    result.push(s[i]);
    i += 1;
  }
  result
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
  /* code modified by LLM (iteration 10): moved ghost variable to proof block and fixed indexing */
  if sy.len() == 1 && sy[0] == '0' {
    let mut result = Vec::new();
    result.push('1');
    return result;
  }
  
  if sy[0] == '1' && sy.len() == 1 {
    let (_, remainder) = div_mod(sx@, sz@);
    return seq_to_vec(remainder);
  }
  
  let highest_bit = find_highest_bit(&sy);
  let n = sy.len() - 1 - highest_bit;
  let power_of_two = create_power_of_two(n);
  
  let result = proof {
    let ghost_n: nat = n as nat;
    mod_exp_pow2(sx@, power_of_two@, ghost_n, sz@)
  };
  seq_to_vec(result)
}
// </vc-code>


}

fn main() {}