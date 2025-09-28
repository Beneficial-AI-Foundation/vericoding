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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
     (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed Vec conversion by using manual conversion from Seq<char> to Vec<char> */
fn div_mod_pow2(num: Vec<char>, n: usize) -> (res: (Vec<char>, Vec<char>))
  requires
    valid_bit_string(num@),
    n >= 0,
  ensures
    valid_bit_string(res.0@) && valid_bit_string(res.1@),
    str2int(res.0@) == str2int(num@) / exp_int(2, n as nat),
    str2int(res.1@) == str2int(num@) % exp_int(2, n as nat),
  decreases n
{
  if n == 0 {
    (num, Vec::new())
  } else {
    let (q, r) = div_mod_pow2(num, n - 1);
    let r_extended = if r.len() > 0 { 
      let mut r_clone = r.clone();
      r_clone.push('0');
      r_clone
    } else { 
      r 
    };
    let (new_q, rem) = div_mod(q@, r_extended@);
    let new_q_vec: Vec<char> = new_q.iter().collect();
    let rem_vec: Vec<char> = rem.iter().collect();
    (new_q_vec, rem_vec)
  }
}

proof fn mod_exp_pow2_helper(x: nat, n: nat, m: nat) -> (res: nat)
  requires
    m > 1,
  ensures
    res == exp_int(x, exp_int(2, n)) % m,
  decreases n
{
  if n == 0 {
    x % m
  } else {
    let prev = mod_exp_pow2_helper(x, (n - 1) as nat, m);
    (prev * prev) % m
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): Fixed Vec conversion by using manual conversion from Seq<char> to Vec<char> */
  let mut result: Vec<char> = Vec::new();
  result.push('1');
  let mut current_base = sx.clone();
  let mut exponent_remaining = sy.clone();
  
  while exponent_remaining.len() > 0
    invariant
      valid_bit_string(result@),
      valid_bit_string(current_base@),
      valid_bit_string(exponent_remaining@),
      str2int(result@) == exp_int(str2int(sx@), (str2int(sy@) as int - str2int(exponent_remaining@) as int) as nat) % str2int(sz@)
    decreases exponent_remaining.len()
  {
    let last_char = exponent_remaining[exponent_remaining.len() - 1];
    exponent_remaining.truncate(exponent_remaining.len() - 1);
    
    if last_char == '1' {
      let temp = mul(result@, current_base@);
      let (q, r) = div_mod(temp, sz@);
      let r_vec: Vec<char> = r.iter().collect();
      result = r_vec;
    }
    
    let temp_base = mul(current_base@, current_base@);
    let (q, r) = div_mod(temp_base, sz@);
    let r_vec: Vec<char> = r.iter().collect();
    current_base = r_vec;
  }
  
  result
}
// </vc-code>


}

fn main() {}