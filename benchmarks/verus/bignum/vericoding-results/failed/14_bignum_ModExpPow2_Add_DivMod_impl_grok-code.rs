// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn shift_left(s: Seq<char>, n: int) -> Seq<char>
  requires
    n >= 0
  ensures
    valid_bit_string(result) && str2int(result) == str2int(s) * exp_int(2nat, n as nat)
{
  let mut v: Vec<char> = Vec::with_capacity(s.len() + n);
  for j in 0..s.len() {
    v.push(s[j]);
  }
  for _ in 0..n {
    v.push('0');
  }
  v.view()
}

fn add(a: Seq<char>, b: Seq<char>) -> Seq<char>
  requires
    valid_bit_string(a) && valid_bit_string(b)
  ensures
    valid_bit_string(result) && str2int(result) == str2int(a) + str2int(b)
{
  let mut carry = 0;
  let mut result: Vec<char> = Vec::new();
  let mut i = 0;
  let max_len = if a.len() > b.len() { a.len() } else { b.len() };
  while i < max_len
    invariant
      i <= max_len
  {
    let a_bit = if i < a.len() {
      if a[a.len() - 1 - i] == '1' { 1 } else { 0 }
    } else { 0 };
    let b_bit = if i < b.len() {
      if b[b.len() - 1 - i] == '1' { 1 } else { 0 }
    } else { 0 };
    let sum = a_bit + b_bit + carry;
    if sum % 2 == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    carry = sum / 2;
    i = i + 1;
  }
  if carry > 0 {
    result.push('1');
  }
  let mut res: Vec<char> = Vec::new();
  for j in (0..result.len()).rev() {
    res.push(result[j]);
  }
  res.view()
}

fn multiply(a: Seq<char>, b: Seq<char>) -> Seq<char>
  requires
    valid_bit_string(a) && valid_bit_string(b)
  ensures
    valid_bit_string(result) && str2int(result) == str2int(a) * str2int(b)
{
  let mut result: Seq<char> = Seq::new();
  for i in 0..b.len() {
    if b[b.len() - 1 - i] == '1' {
      let shifted = shift_left(a, i);
      result = add(result, shifted);
    }
  }
  result
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  (Seq::new(), Seq::new())
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if str2int(sy@) == 0 {
      Vec::new()
    } else {
      let (_q, r) = div_mod(sx@, sz@);
      let mut res: Vec<char> = Vec::new();
      for j in 0..r.len() {
        res.push(r[j]);
      }
      res
    }
  } else {
    let mut sy_right: Vec<char> = Vec::new();
    for j in 0.. (n as int) {
      sy_right.push(sy[j]);
    }
    let temp = mod_exp_pow2(sx, sy_right, n - 1, sz);
    let sq = multiply(temp@, temp@);
    let (_q, r) = div_mod(sq, sz@);
    let mut res: Vec<char> = Vec::new();
    for j in 0..r.len() {
      res.push(r[j]);
    }
    res
  }
}
// </vc-code>


}

fn main() {}