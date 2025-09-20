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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}