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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) * str2_int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>

proof fn mod_exp_invariant(sx: &Seq<char>, sy: &Seq<char>, sz: &Seq<char>, i: int) -> (result: nat)
  requires
    valid_bit_string(*sx) && valid_bit_string(*sy) && valid_bit_string(*sz),
    sy.len() > 0 && str2_int(*sz) > 1,
    0 <= i && i <= sy.len(),
  ensures
    result == exp_int(str2_int(*sx), str2_int(sy.subrange(i as nat, sy.len() as nat))) % str2_int(*sz),
  decreases sy.len() - i as nat,
{
  if i == sy.len() {
      1nat % str2_int(*sz)
  } else {
      let current_bit = if sy[i as usize] == '1' { 1nat } else { 0nat };
      let partial = mod_exp_invariant(sx, sy, sz, i + 1);
      ((partial * partial) % str2_int(*sz) * exp_int(str2_int(*sx), current_bit)) % str2_int(*sz)
  }
}

fn mod_exp_helper(a: Vec<char>, b: Vec<char>, n: Vec<char>, i: usize) -> (result: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@) && valid_bit_string(n@),
    n@.len() > 0 && str2_int(n@) > 1,
    i <= b@.len(),
  ensures
    valid_bit_string(result@) &&
    str2_int(result@) == exp_int(str2_int(a@), str2_int(b@.subrange(i, b@.len()))) % str2_int(n@),
  decreases b@.len() - i,
{
  if i == b.len() {
      let mut res = Vec::new();
      res.push('1');
      res
  } else {
      let partial = mod_exp_helper(a.clone(), b.clone(), n.clone(), i + 1);
      let squared = mul(partial@, partial@);
      let squared_mod = div_mod(squared, n@);
      
      if b[i] == '1' {
          let temp = mul(squared_mod@, a@);
          div_mod(temp, n@)
      } else {
          squared_mod
      }
  }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (remainder: Vec<char>)
  requires
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    divisor.len() > 0 && str2_int(divisor) > 0,
  ensures
    valid_bit_string(remainder@) &&
    str2_int(remainder@) == str2_int(dividend) % str2_int(divisor),
{
  if str2_int(dividend) < str2_int(divisor) {
      let mut result = Vec::new();
      if str2_int(dividend) == 0 {
          result.push('0');
      } else {
          let mut idx = 0;
          while idx < dividend.len() {
              result.push(dividend[idx as usize]);
              idx += 1;
          }
      }
      result
  } else {
      let mut current_int = str2_int(dividend);
      let div_val = str2_int(divisor);
      
      while current_int >= div_val {
          current_int = current_int - div_val;
      }
      
      let mut result = Vec::new();
      if current_int == 0 {
          result.push('0');
      } else {
          let bits = int_to_bit_string(current_int);
          let mut idx = 0;
          while idx < bits.len() {
              result.push(bits[idx as usize]);
              idx += 1;
          }
      }
      result
  }
}

spec fn int_to_bit_string(n: nat) -> Seq<char> {
  if n == 0 {
      seq!['0']
  } else {
      let mut s = int_to_bit_string(n / 2);
      s = s.push(if n % 2 == 1 { '1' } else { '0' });
      s
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
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches and invalid method calls */
    let result = mod_exp_helper(sx, sy, sz, 0);
    result
}
// </vc-code>


}

fn main() {}