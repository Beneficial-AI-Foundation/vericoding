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
/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires {
      valid_bit_string(s1) && valid_bit_string(s2),
  }
  ensures {
      valid_bit_string(res),
      str2int(res) == str2int(s1) + str2int(s2),
  }
{
  let mut carry = 0;
  let mut i = 0;
  let mut result = Vec::new();
  
  while i < s1.len() || i < s2.len() || carry != 0
    invariant carry == 0 || carry == 1,
  {
    let a = if i < s1.len() { if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
    let b = if i < s2.len() { if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
    let sum = a + b + carry;
    carry = sum / 2;
    let bit = sum % 2;
    if bit == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    i += 1;
  }
  
  let mut final_result = Vec::new();
  for j in (0..result.len()).rev() {
    final_result.push(result[j]);
  }
  
  let mut seq_result = Seq::empty();
  for j in 0..final_result.len() {
    seq_result.push(final_result[j]);
  }
  seq_result
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn shift_left(s: Seq<char>, n: nat) -> (res: Seq<char>)
  requires {
      valid_bit_string(s),
  }
  ensures {
      valid_bit_string(res),
      str2int(res) == str2int(s) * exp_int(2, n),
  }
{
  let mut res = s;
  for _i in 0..n {
    res = res.push('0');
  }
  res
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires {
      valid_bit_string(s1) && valid_bit_string(s2),
  }
  ensures {
      valid_bit_string(res),
      str2int(res) == str2int(s1) * str2int(s2),
  }
{
  let mut result = seq!['0'];
  let s2_rev = reverse(s2);
  
  for j in 0..s2_rev.len() {
    if s2_rev[j] == '1' {
      let shifted = shift_left(s1, j);
      result = add(result, shifted);
    }
  }
  result
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn reverse(s: Seq<char>) -> (res: Seq<char>)
  requires {
      valid_bit_string(s),
  }
  ensures {
      valid_bit_string(res),
      forall|i: int| 0 <= i < s.len() ==> res[i] == s[s.len()-1-i],
  }
{
  let mut rev = Seq::empty();
  for i in (0..s.len()).rev() {
    rev.push(s[i]);
  }
  rev
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires {
      valid_bit_string(s1) && valid_bit_string(s2),
      str2int(s1) >= str2int(s2),
  }
  ensures {
      valid_bit_string(res),
      str2int(res) == str2int(s1) - str2int(s2),
  }
{
  let mut borrow = 0;
  let mut result = Vec::new();
  
  for i in 0..s1.len() {
    let a = if i < s1.len() { if s1[s1.len()-1-i] == '1' { 1 } else { 0 } } else { 0 };
    let b = if i < s2.len() { if s2[s2.len()-1-i] == '1' { 1 } else { 0 } } else { 0 };
    let diff = a - b - borrow;
    if diff < 0 {
      borrow = 1;
      result.push(if (diff + 2) == 1 { '1' } else { '0' });
    } else {
      borrow = 0;
      result.push(if diff == 1 { '1' } else { '0' });
    }
  }
  
  let mut final_result = Vec::new();
  for j in (0..result.len()).rev() {
    final_result.push(result[j]);
  }
  
  let mut seq_result = Seq::empty();
  for j in 0..final_result.len() {
    seq_result.push(final_result[j]);
  }
  seq_result
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: int)
  requires {
      valid_bit_string(s1) && valid_bit_string(s2),
  }
  ensures {
      (res == -1 && str2int(s1) < str2int(s2)) ||
      (res == 0 && str2int(s1) == str2int(s2)) ||
      (res == 1 && str2int(s1) > str2int(s2)),
  }
{
  if s1.len() > s2.len() {
    1
  } else if s1.len() < s2.len() {
    -1
  } else {
    for i in 0..s1.len() {
      if s1[i] == '1' && s2[i] == '0' {
        return 1;
      } else if s1[i] == '0' && s2[i] == '1' {
        return -1;
      }
    }
    0
  }
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires {
      valid_bit_string(dividend) && valid_bit_string(divisor),
      str2int(divisor) > 0,
  }
  ensures {
      valid_bit_string(res.0) && valid_bit_string(res.1),
      str2int(res.0) == str2int(dividend) / str2int(divisor),
      str2int(res.1) == str2int(dividend) % str2int(divisor),
  }
{
  let mut remainder = seq!['0'];
  let mut quotient = Seq::empty();
  
  for i in 0..dividend.len() {
    let doubled = shift_left(remainder, 1);
    let current_bit = if dividend[i] == '1' { seq!['1'] } else { seq!['0'] };
    let temp = add(doubled, current_bit);
    
    if compare(temp, divisor) >= 0 {
      quotient.push('1');
      remainder = sub(temp, divisor);
    } else {
      quotient.push('0');
      remainder = temp;
    }
  }
  
  (quotient, remainder)
}

/* helper modified by LLM (iteration 7): fixed requires/ensures block syntax */
fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires {
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
      str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
      sy.len() == n + 1,
      str2int(sz) > 1,
  }
  ensures {
      valid_bit_string(res),
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  }
{
  if str2int(sy) == 0 {
    let (_, rem) = div_mod(seq!['1'], sz);
    rem
  } else {
    let mut result = sx;
    for _i in 0..n {
      result = mul(result, result);
      let (_, rem) = div_mod(result, sz);
      result = rem;
    }
    result
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
  /* code modified by LLM (iteration 3): fixed mod_exp implementation with proper recursion */
  let sx_seq = sx@;
  let sy_seq = sy@;
  let sz_seq = sz@;
  
  if sy_seq.len() == 1 {
    if sy_seq[0] == '0' {
      let (_, remainder) = div_mod(seq!['1'], sz_seq);
      let mut res_vec = Vec::new();
      for i in 0..remainder.len() {
        res_vec.push(remainder[i]);
      }
      res_vec
    } else {
      let (_, remainder) = div_mod(sx_seq, sz_seq);
      let mut res_vec = Vec::new();
      for i in 0..remainder.len() {
        res_vec.push(remainder[i]);
      }
      res_vec
    }
  } else {
    let rest = sy_seq.subrange(0, sy_seq.len()-1);
    let last_bit = sy_seq[sy_seq.len()-1];
    
    let mut rest_vec = Vec::new();
    for i in 0..rest.len() {
      rest_vec.push(rest[i]);
    }
    
    let temp = mod_exp(sx.clone(), rest_vec, sz.clone());
    let temp_seq = temp@;
    
    let temp_sq = mul(temp_seq, temp_seq);
    
    let base = if last_bit == '1' {
      mul(temp_sq, sx_seq)
    } else {
      temp_sq
    };
    
    let (_, remainder) = div_mod(base, sz_seq);
    
    let mut res_vec = Vec::new();
    for i in 0..remainder.len() {
      res_vec.push(remainder[i]);
    }
    res_vec
  }
}
// </vc-code>


}

fn main() {}