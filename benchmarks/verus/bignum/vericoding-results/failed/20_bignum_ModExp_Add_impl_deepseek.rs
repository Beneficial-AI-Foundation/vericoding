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
/* helper modified by LLM (iteration 10): Fixed nat literal syntax and type conversions, replaced nat with u64 in executable code */
proof fn mod_exp_lemma(x: nat, y: nat, z: nat) 
  requires z > 1,
  ensures exp_int(x, y) % z == if y > 0 { (x % z) * exp_int(x % z, (y - 1) as nat) % z } else { 1 % z },
decreases y
{
  if y > 0 {
    mod_exp_lemma(x, (y - 1) as nat, z);
  }
}

spec fn char_at(s: Seq<char>, i: int) -> char
  requires 0 <= i < s.len()
{
  s.index(i)
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
  ensures res@ == s
{
  let mut vec = Vec::new();
  let mut i: usize = 0;
  while i < s.len() as usize
    invariant
      0 <= i <= s.len(),
      vec@ == s.subrange(0, i as int)
  {
    vec.push(char_at(s, i as int));
    i = i + 1;
  }
  vec
}

fn bit_string_mod(s: Vec<char>, z: nat) -> (res: Vec<char>)
  requires valid_bit_string(s@) && z > 1,
  ensures valid_bit_string(res@) && str2int(res@) == str2int(s@) % z,
{
  let mut remainder: u64 = 0;
  let mut result_vec = Vec::new();
  
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      remainder < z,
      valid_bit_string(result_vec@),
      str2int(result_vec@) * exp_int(2, (s.len() - i) as nat) + remainder as nat == str2int(s@.subrange(0, i as int)) % z
  {
    remainder = remainder * 2 + (if char_at(s@, i as int) == '1' { 1 } else { 0 });
    if remainder >= z as u64 {
      remainder = remainder - z as u64;
      result_vec.push('1');
    } else {
      result_vec.push('0');
    }
    i = i + 1;
  }
  
  if remainder > 0 {
    let mut temp_vec = Vec::new();
    let mut r = remainder;
    while r > 0
      invariant
        r >= 0,
        valid_bit_string(temp_vec@),
        str2int(temp_vec@) == r as nat
    {
      if r % 2 == 1 {
        temp_vec.push('1');
      } else {
        temp_vec.push('0');
      }
      r = r / 2;
    }
    temp_vec = temp_vec.into_iter().rev().collect();
    result_vec = temp_vec;
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
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type conversions and Seq operations */
{
    if sy.len() == 0 {
        let one_mod_z = bit_string_mod(vec!['1'], str2int(sz@));
        one_mod_z
    } else {
        let y_last = char_at(sy@, (sy.len() - 1) as int);
        let sy_minus_one: Vec<char> = seq_to_vec(sy@.subrange(0, (sy.len() - 1) as int));
        
        let x_mod_z = bit_string_mod(sx.clone(), str2int(sz@));
        
        let exp_minus_one = mod_exp(sx.clone(), sy_minus_one, sz.clone());
        
        if y_last == '1' {
            let temp = add(exp_minus_one@, seq_to_vec(Seq::new(0, |i: int| '0')));
            let x_bits = x_mod_z;
            let result = add(temp, x_bits@);
            let result_vec = seq_to_vec(result);
            bit_string_mod(result_vec, str2int(sz@))
        } else {
            let squared = add(exp_minus_one@, exp_minus_one@);
            let squared_vec = seq_to_vec(squared);
            bit_string_mod(squared_vec, str2int(sz@))
        }
    }
}
// </vc-code>


}

fn main() {}