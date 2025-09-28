// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): add decreases clauses to loops */
fn add_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) + str2int(s2@)
{
  let mut res = Vec::new();
  let mut carry = false;
  let mut i = s1.len();
  let mut j = s2.len();
  
  while i > 0 || j > 0 || carry
      decreases (i + j + if carry { 1 } else { 0 }) as nat
  {
    let d1 = if i > 0 {
      i -= 1;
      if s1[i] == '1' { 1 } else { 0 }
    } else { 0 };
    
    let d2 = if j > 0 {
      j -= 1;
      if s2[j] == '1' { 1 } else { 0 }
    } else { 0 };
    
    let sum = d1 + d2 + (if carry { 1 } else { 0 });
    carry = sum >= 2;
    res.push(if sum % 2 == 1 { '1' } else { '0' });
  }
  
  // Reverse the vector manually
  let mut reversed = Vec::new();
  let mut idx = res.len();
  while idx > 0 {
    idx -= 1;
    reversed.push(res[idx]);
  }
  res = reversed;
  while res.len() > 1 && res[0] == '0' {
    res.remove(0);
  }
  res
}

/* helper modified by LLM (iteration 10): add decreases clauses to loops */
fn sub_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@) && valid_bit_string(s2@) && str2int(s1@) >= str2int(s2@)
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) - str2int(s2@)
{
  let mut res = Vec::new();
  let mut borrow = false;
  let mut i = s1.len();
  let mut j = s2.len();
  
  while i > 0 || j > 0
      decreases (i + j) as nat
  {
    let d1 = if i > 0 {
      i -= 1;
      if s1[i] == '1' { 1 } else { 0 }
    } else { 0 };
    
    let d2 = if j > 0 {
      j -= 1;
      if s2[j] == '1' { 1 } else { 0 }
    } else { 0 };
    
    let mut diff = d1 - d2 - (if borrow { 1 } else { 0 });
    if diff < 0 {
      diff += 2;
      borrow = true;
    } else {
      borrow = false;
    }
    res.push(if diff == 1 { '1' } else { '0' });
  }
  
  // Reverse the vector manually
  let mut reversed = Vec::new();
  let mut idx = res.len();
  while idx > 0 {
    idx -= 1;
    reversed.push(res[idx]);
  }
  res = reversed;
  while res.len() > 1 && res[0] == '0' {
    res.remove(0);
  }
  res
}

fn cmp_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures (res == -1 && str2int(s1@) < str2int(s2@)) || 
          (res == 0 && str2int(s1@) == str2int(s2@)) || 
          (res == 1 && str2int(s1@) > str2int(s2@))
{
  if s1.len() > s2.len() {
    1
  } else if s1.len() < s2.len() {
    -1
  } else {
    let mut i = 0;
    while i < s1.len() {
      if s1[i] != s2[i] {
        return if s1[i] == '1' { 1 } else { -1 };
      }
      i += 1;
    }
    0
  }
}

fn shift_left(s: &Vec<char>, n: usize) -> (res: Vec<char>)
  requires valid_bit_string(s@)
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s@) * exp_int(2, n as nat)
{
  let mut res = s.clone();
  for _ in 0..n {
    res.push('0');
  }
  res
}

fn mul_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) * str2int(s2@)
{
  if s1.len() == 1 && s1[0] == '0' || s2.len() == 1 && s2[0] == '0' {
    return vec!['0'];
  }
  
  let mut res = vec!['0'];
  let mut i = 0;
  while i < s2.len() {
    if s2[i] == '1' {
      let shifted = shift_left(s1, s2.len() - 1 - i);
      res = add_bit_strings(&res, &shifted);
    }
    i += 1;
  }
  res
}

fn mod_bit_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@) && valid_bit_string(s2@) && str2int(s2@) > 0
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) % str2int(s2@)
{
  if s1.len() == 1 && s1[0] == '0' {
    return vec!['0'];
  }
  
  let mut res = s1.clone();
  while cmp_bit_strings(&res, s2) >= 0 {
    res = sub_bit_strings(&res, s2);
  }
  res
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): no changes needed in this iteration */
{
  if sy.len() == 1 && sy[0] == '0' {
    vec!['1']
  } else {
    let mut rest = Vec::new();
    for i in 1..sy.len() {
      rest.push(sy[i]);
    }
    let half = mod_exp(sx.clone(), rest, sz.clone());
    let square = mul_bit_strings(&half, &half);
    let square_mod = mod_bit_strings(&square, &sz);
    
    if sy[0] == '1' {
      let mul = mul_bit_strings(&square_mod, &sx);
      mod_bit_strings(&mul, &sz)
    } else {
      square_mod
    }
  }
}
// </vc-code>


}

fn main() {}