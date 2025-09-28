// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s.index(s.len() - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s.index(i) == '0' || s.index(i) == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed int to isize in loop variables and replaced subrange with slicing */
fn add_vec(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@),
  ensures
    valid_bit_string(res@) &&
    str2int(res@) == str2int(a@) + str2int(b@),
{
  let mut carry = 0;
  let mut i = (a.len() as isize) - 1;
  let mut j = (b.len() as isize) - 1;
  let mut result = Vec::new();

  while i >= 0 || j >= 0 || carry > 0
    invariant
      i >= -1 && j >= -1 && (carry == 0 || carry == 1),
      // Invariant: current result + carry * 2^(k) = a[0..i+1] + b[0..j+1]
      // where k is the number of bits processed so far
  {
    let x = if i >= 0 { if a[i as usize] == '1' { 1 } else { 0 } } else { 0 };
    let y = if j >= 0 { if b[j as usize] == '1' { 1 } else { 0 } } else { 0 };
    let sum = x + y + carry;
    carry = sum / 2;
    let bit = sum % 2;
    result.push(if bit == 1 { '1' } else { '0' });
    if i >= 0 { i -= 1; }
    if j >= 0 { j -= 1; }
  }

  result.reverse();
  result
}

/* helper modified by LLM (iteration 2): replaced subrange with slicing */
fn mul_vec(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@),
  ensures
    valid_bit_string(res@) &&
    str2int(res@) == str2int(a@) * str2int(b@),
{
  if a.len() == 0 || b.len() == 0 {
    vec![]
  } else {
    let a_last = a[a.len()-1];
    let a_rest = a[0..a.len()-1].to_vec();
    let b_rest = b[0..b.len()-1].to_vec();
    let mut part1 = mul_vec(a_rest, b);
    let mut part2 = mul_vec(vec![a_last], b_rest);
    let mut part3 = add_vec(part1, part2);
    part3.push(a_last);
    part3
  }
}

/* helper modified by LLM (iteration 2): replaced subrange with slicing */
fn mod_vec(a: Vec<char>, m: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(m@) &&
    str2int(m@) > 0,
  ensures
    valid_bit_string(res@) &&
    str2int(res@) == str2int(a@) % str2int(m@) &&
    str2int(res@) < str2int(m@),
{
  if a.len() == 0 {
    vec![]
  } else {
    let a_last = a[a.len()-1];
    let a_rest = a[0..a.len()-1].to_vec();
    let mut temp = mod_vec(a_rest, m);
    temp.push(a_last);
    let mut doubled = add_vec(temp, temp);
    if doubled.len() >= m.len() || (doubled.len() == m.len() && doubled >= m) {
      doubled = mod_vec(doubled, m);
    }
    doubled
  }
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
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatch in invariant by casting i to int */
{
  let mut res = vec!['1'];
  let base = sx;
  let modulus = sz;

  for i in 0..sy.len()
    invariant
      valid_bit_string(res@) &&
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@.subrange(0, i as int))) % str2int(sz@),
  {
    // Square the result
    res = mul_vec(res, res);
    res = mod_vec(res, modulus);

    // If the current bit is '1', multiply by the base
    if sy[i] == '1' {
      res = mul_vec(res, base);
      res = mod_vec(res, modulus);
    }
  }

  res
}
// </vc-code>


}

fn main() {}