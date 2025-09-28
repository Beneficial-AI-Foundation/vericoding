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
spec fn mod_exp_helper(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 {
    1 % z
  } else if y % 2 == 0 {
    let half = mod_exp_helper(x, y / 2, z);
    (half * half) % z
  } else {
    (x * mod_exp_helper(x, y - 1, z)) % z
  }
}

proof fn lemma_mod_exp_correct(x: nat, y: nat, z: nat)
  requires
    z > 1,
  ensures
    mod_exp_helper(x, y, z) == exp_int(x, y) % z
  decreases y
{
  if y == 0 {
    assert(exp_int(x, 0) == 1;
    assert(1 % z == 1;
  } else if y % 2 == 0 {
    let half = y / 2;
    lemma_mod_exp_correct(x, half, z);
    calc! {
      (mod_exp_helper(x, half, z) * mod_exp_helper(x, half, z)) % z;
      == { assert(mod_exp_helper(x, half, z) == exp_int(x, half) % z); }
      ((exp_int(x, half) % z) * (exp_int(x, half) % z)) % z;
      == { assert((a % z * b % z) % z == (a * b) % z); }
      (exp_int(x, half) * exp_int(x, half)) % z;
      == { assert(exp_int(x, half) * exp_int(x, half) == exp_int(x, half + half)); }
      exp_int(x, half + half) % z;
      == { assert(half + half == y); }
      exp_int(x, y) % z;
    }
  } else {
    lemma_mod_exp_correct(x, y - 1, z);
    calc! {
      (x * mod_exp_helper(x, y - 1, z)) % z;
      == { assert(mod_exp_helper(x, y - 1, z) == exp_int(x, y - 1) % z); }
      (x * (exp_int(x, y - 1) % z)) % z;
      == { assert((a * (b % z)) % z == (a * b) % z); }
      (x * exp_int(x, y - 1)) % z;
      == { assert(x * exp_int(x, y - 1) == exp_int(x, y)); }
      exp_int(x, y) % z;
    }
  }
}

proof fn lemma_exp_int_pos(x: nat, y: nat)
  ensures
    exp_int(x, y) >= 1
  decreases y
{
  if y == 0 {
    assert(exp_int(x, 0) == 1);
  } else {
    lemma_exp_int_pos(x, y - 1);
    assert(exp_int(x, y) == x * exp_int(x, y - 1));
    assert(exp_int(x, y - 1) >= 1);
    assert(x * exp_int(x, y - 1) >= 1 * 1);
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
{
    let x = str2int(sx@);
    let y = str2int(sy@);
    let z = str2int(sz@);
    
    proof {
        lemma_mod_exp_correct(x, y, z);
    }
    
    let result_nat = mod_exp_helper(x, y, z);
    
    // Convert nat back to bit string
    let mut result_vec: Vec<char> = Vec::new();
    let mut n = result_nat;
    
    while n > 0
        invariant
            n >= 0,
            result_vec@.len() + n.len() == result_nat.len() || result_nat == 0,
            str2int(result_vec@) * exp_int(2, n.len()) + n == result_nat,
        decreases n
    {
        if n % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        n = n / 2;
    }
    
    if result_vec.len() == 0 {
        result_vec.push('0');
    }
    
    // Reverse to get correct bit order
    result_vec.reverse();
    
    result_vec
}
// </vc-code>


}

fn main() {}