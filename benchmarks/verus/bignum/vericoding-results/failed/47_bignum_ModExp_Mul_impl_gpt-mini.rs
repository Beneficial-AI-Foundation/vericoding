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
spec fn vec_to_nat(v: Vec<char>) -> nat { str2int(v@) }

fn nat_to_vec(n: nat) -> (v: Vec<char>)
  ensures
    valid_bit_string(v@) &&
    str2int(v@) == n
{
  let mut x = n;
  let mut bits: Vec<char> = Vec::new();
  if x == 0 {
    bits.push('0');
    bits
  } else {
    while x > 0
      invariant
        x >= 0,
      decreases x
    {
      if x % 2 == 1 {
        bits.push('1');
      } else {
        bits.push('0');
      }
      x = x / 2;
    }
    let mut res: Vec<char> = Vec::new();
    let mut i = bits.len();
    while i > 0
      invariant
        0 <= i <= bits.len(),
      decreases i
    {
      i -= 1;
      res.push(bits.get(i));
    }
    res
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
{
  let m = vec_to_nat(sz);
  // m > 1 by precondition
  let mut result_nat: nat = 1 % m;
  let mut b = vec_to_nat(sx) % m;
  let mut e = vec_to_nat(sy);
  while e > 0
      invariant
        e >= 0,
      decreases e
  {
    if e % 2 == 1 {
      result_nat = (result_nat * b) % m;
    }
    e = e / 2;
    b = (b * b) % m;
  }
  nat_to_vec(result_nat)
}

// </vc-code>


}

fn main() {}