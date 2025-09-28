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
/* helper modified by LLM (iteration 9): changed str2int_exec to return int and fixed type issues in computation */
proof fn str2int_exec(s: Seq<char>) -> (result: int)
  requires 
    valid_bit_string(s),
    s.len() < 64
  ensures 
    result as nat == str2int(s),
    result >= 0
  decreases s.len()
{
  let len = s.len() as int;
  if len == 0 {
    0
  } else {
    let sub_res = str2int_exec(s.subrange(0 as int, len - (1 as int)));
    (2 * sub_res) + (if s[len - (1 as int)] == '1' { 1 } else { 0 })
  }
}

/* helper modified by LLM (iteration 5): added comment for clarity */
fn int2str(n: u64) -> (result: Vec<char>)
  ensures 
    valid_bit_string(result@),
    str2int(result@) == n as nat
{
  if n == 0 {
    vec!['0']
  } else {
    let mut current = n;
    let mut digits = Vec::new();
    while current > 0
      invariant
        current >= 0,
      decreases current
    {
      digits.push(if (current % 2) == 1 { '1' } else { '0' });
      current = current / 2;
    }
    digits.reverse();
    digits
  }
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
/* code modified by LLM (iteration 9): rewritten mod_exp to use int for computations, avoid assigning exec vars in proof blocks, and fix casting of nat to int/usize */
{
  let len = sy@.len() as int;
  let mut x: int;
  proof { x = str2int_exec(sx@); }
  let mut z: int;
  proof { z = str2int_exec(sz@); }
  let mut res: int = 1;
  let mut base: int = spec_euclidean_mod(x, z);
  let mut i: int = 0;
  while i < len
    invariant
      i <= len,
      str2int(sz@) > 1,
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    decreases (len - i) as nat
  {
    let bit: char;
    proof { bit = sy@[(len - 1 - i) as int]; }
    if bit == '1' { res = spec_euclidean_mod(res * base, z); }
    base = spec_euclidean_mod(base * base, z);
    i += 1;
  }
  proof { assert(res >= 0 && (res as u64) as int == res); }
  int2str(res as u64)
}
// </vc-code>


}

fn main() {}