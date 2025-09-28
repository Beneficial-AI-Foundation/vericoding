// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1) &&
    str2int(ret.0) == str2int(dividend) / str2int(divisor) &&
    str2int(ret.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `pure` keyword, `exp_int` call had `int` not `nat` types. */
proof fn lemma_mod_exp_matches_exp_int_mod(x: nat, y: nat, z: nat)
  ensures mod_exp_spec(x, y, z) == exp_int(x, y) % z
  decreases y
{
  if y == 0 {
  } else if y % 2 == 0 {
    let half_y = (y / 2) as nat;
    lemma_mod_exp_matches_exp_int_mod(x, half_y, z);
  } else {
    lemma_mod_exp_matches_exp_int_mod(x, (y - 1) as nat, z);
  }
}
spec fn mod_exp_spec(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 {
    1nat % z
  } else if y % 2 == 0 { // y is even
    let half_y = (y / 2) as nat;
    let res = mod_exp_spec(x, half_y, z);
    (res * res) % z
  } else { // y is odd
    (x * mod_exp_spec(x, (y - 1) as nat, z)) % z
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
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Cast `temp` to `u64` before using `temp as nat` in `Seq::new` and indexing with `usize`. */
{
  let x = str2int(sx@);
  let y = str2int(sy@);
  let z = str2int(sz@);

  proof {
    lemma_mod_exp_matches_exp_int_mod(x, y, z);
  }

  let final_res_nat = mod_exp_spec(x, y, z);
  let mut bit_string: Seq<char> = Seq::empty();
  let mut temp: u64 = final_res_nat as u64;

  if temp == 0 {
    bit_string = bit_string.add(Seq::new(1nat, |i| '0'))
  } else {
    while temp > 0
      invariant
        temp >= 0
      decreases temp
    {
      if temp % 2 == 1 {
        bit_string = Seq::new(1nat, |i| '1').add(bit_string);
      } else {
        bit_string = Seq::new(1nat, |i| '0').add(bit_string);
      }
      temp = temp / 2;
    }
  }

  // Convert Seq<char> to Vec<char>
  let mut result_vec = Vec::new();
  let mut i = 0usize;
  while i < bit_string.len()
    invariant
      0 <= i,
      i as nat <= bit_string.len(),
      result_vec.len() == i,
      forall|j: int| 0 <= j < i ==> result_vec[j] == bit_string[j as nat]
    decreases bit_string.len() - i as nat
  {
    result_vec.push(bit_string.index(i as nat));
    i = i + 1;
  }
  result_vec
}
// </vc-code>


}

fn main() {}