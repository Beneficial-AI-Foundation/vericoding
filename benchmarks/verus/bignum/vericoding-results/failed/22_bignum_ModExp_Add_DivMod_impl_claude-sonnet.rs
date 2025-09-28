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
/* helper modified by LLM (iteration 10): Fixed nat suffix errors and int type casting */
fn mod_exp_helper(base: Seq<char>, exp: Seq<char>, modulus: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(base) && valid_bit_string(exp) && valid_bit_string(modulus),
    exp.len() > 0,
    str2_int(modulus) > 1
  ensures
    valid_bit_string(res),
    str2_int(res) == exp_int(str2_int(base), str2_int(exp)) % str2_int(modulus)
  decreases exp.len()
{
  if exp.len() == 1 && exp.index(0int) == '0' {
    seq!['1']
  } else {
    let half_exp_len = (exp.len() - 1) as int;
    let half_exp = exp.subrange(0int, half_exp_len);
    let last_bit = exp.index(half_exp_len);
    
    if half_exp.len() == 0 {
      let (_, remainder) = div_mod(base, modulus);
      remainder
    } else {
      let half_result = mod_exp_helper(base, half_exp, modulus);
      let squared = {
        let temp = add(half_result, half_result);
        let (_, remainder) = div_mod(temp, modulus);
        remainder
      };
      
      if last_bit == '0' {
        squared
      } else {
        let multiplied = {
          let temp_base = {
            let (_, remainder) = div_mod(base, modulus);
            remainder
          };
          let product = add(squared, temp_base);
          let (_, remainder) = div_mod(product, modulus);
          remainder
        };
        multiplied
      }
    }
  }
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
  /* code modified by LLM (iteration 10): Fixed nat casting and Seq indexing errors */
  let result = mod_exp_helper(sx@, sy@, sz@);
  let mut vec_result = Vec::new();
  let mut i: usize = 0;
  while i < result.len()
    invariant
      0 <= i <= result.len(),
      vec_result.len() == i,
      forall|j: int| 0 <= j < i ==> vec_result[j] == result[j as int]
  {
    proof {
      assert(0 <= i < result.len());
    }
    vec_result.push(result[i as int]);
    i = i + 1;
  }
  vec_result
}
// </vc-code>


}

fn main() {}