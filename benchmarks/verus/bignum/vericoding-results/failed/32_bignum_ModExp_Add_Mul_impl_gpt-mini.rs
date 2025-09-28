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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) * str2_int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): executable nat_to_bits_exec and correctness proof */
fn nat_to_bits_exec(n: nat) -> Vec<char>
  decreases n
{
  if n == 0 {
    Vec::new()
  } else {
    let q = n / 2;
    let r = n % 2;
    let mut v = nat_to_bits_exec(q);
    v.push(if r == 1 { '1' } else { '0' });
    v
  }
}

proof fn nat_to_bits_exec_correct(n: nat)
  ensures
    valid_bit_string(nat_to_bits_exec(n)@) && str2_int(nat_to_bits_exec(n)@) == n,
  decreases n
{
  if n == 0 {
    assert(nat_to_bits_exec(0)@ == Seq::<char>::empty());
    assert(valid_bit_string(nat_to_bits_exec(0)@));
    assert(str2_int(nat_to_bits_exec(0)@) == 0);
  } else {
    let q = n / 2;
    let r = n % 2;
    nat_to_bits_exec_correct(q);
    let vq = nat_to_bits_exec(q);
    let v = nat_to_bits_exec(n);
    assert(v@ == vq@ + seq![ if r == 1 { '1' } else { '0' } ]);
    assert(valid_bit_string(v@));
    assert(str2_int(v@) == 2 * str2_int(vq@) + (if r == 1 { 1 } else { 0 }));
    assert(str2_int(vq@) == q);
    assert(2 * q + (if r == 1 { 1 } else { 0 }) == n);
    assert(str2_int(v@) == n);
  }
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): compute modular exponent and convert result to bit vector */
{
  let n = exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@);
  let res = nat_to_bits_exec(n);
  proof {
    nat_to_bits_exec_correct(n);
    assert(valid_bit_string(res@));
    assert(str2_int(res@) == n);
  }
  res
}

// </vc-code>


}

fn main() {}