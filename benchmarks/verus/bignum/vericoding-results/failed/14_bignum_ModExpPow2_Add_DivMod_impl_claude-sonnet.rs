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
/* helper modified by LLM (iteration 10): fixed compilation errors by using usize for loop and proper Vec indexing */
fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
  ensures res@ == s
{
  let mut v = Vec::new();
  let mut i: usize = 0;
  while i < s.len() as usize
    invariant
      0 <= i <= s.len(),
      v@.len() == i,
      forall|j: int| 0 <= j < i ==> v@[j] == s[j]
  {
    v.push(s[i as int]);
    i = i + 1;
  }
  v
}

fn vec_to_seq(v: &Vec<char>) -> (res: Seq<char>)
  ensures res == v@
{
  v@
}

fn is_zero(s: &Vec<char>) -> (res: bool)
  requires valid_bit_string(s@)
  ensures res == (str2int(s@) == 0)
{
  s.len() == 0 || (s.len() == 1 && s[0] == '0')
}

fn bit_string_one() -> (res: Vec<char>)
  ensures valid_bit_string(res@) && str2int(res@) == 1
{
  vec!['1']
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
  /* code modified by LLM (iteration 10): simplified implementation using only divide-and-conquer approach */
  if n == 0 {
    if is_zero(&sy) {
      return vec!['1'];
    } else {
      return vec!['1'];
    }
  }
  
  if is_zero(&sy) {
    return vec!['1'];
  }
  
  let half_exp = mod_exp_pow2(sx.clone(), sy.clone(), n - 1, sz.clone());
  let squared_seq = seq_to_vec(add(half_exp@, half_exp@));
  let (_, remainder) = div_mod(squared_seq@, sz@);
  seq_to_vec(remainder)
}
// </vc-code>


}

fn main() {}