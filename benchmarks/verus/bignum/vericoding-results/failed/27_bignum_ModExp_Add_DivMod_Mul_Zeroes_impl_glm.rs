// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix nat type usage in executable code */
proof fn lemma_mod_exp_helper(x: nat, y: nat, z: nat)
  requires
    z > 1,
  ensures
    exp_int(x, y) % z == mod_exp_helper(x, y, z)
  decreases y
{
  if y == 0 {
    assert(exp_int(x, 0) == 1);
    assert(exp_int(x, 0) % z == 1nat % z);
    assert(1nat % z == mod_exp_helper(x, 0, z));
  } else {
    let half = y / 2;
    lemma_mod_exp_helper(x, half, z);
    
    if y % 2 == 0 {
      // y is even
      assert(exp_int(x, y) == exp_int(x, half) * exp_int(x, half));
      assert(exp_int(x, y) % z == (exp_int(x, half) % z * exp_int(x, half) % z) % z);
      assert(exp_int(x, half) % z == mod_exp_helper(x, half, z));
      assert(exp_int(x, y) % z == (mod_exp_helper(x, half, z) * mod_exp_helper(x, half, z)) % z);
    } else {
      // y is odd
      assert(exp_int(x, y) == exp_int(x, half) * exp_int(x, half) * x);
      assert(exp_int(x, y) % z == ((exp_int(x, half) % z * exp_int(x, half) % z) % z * (x % z)) % z);
      assert(exp_int(x, half) % z == mod_exp_helper(x, half, z));
      assert(exp_int(x, y) % z == ((mod_exp_helper(x, half, z) * mod_exp_helper(x, half, z)) % z * (x % z)) % z);
    }
  }
}

spec fn mod_exp_helper(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 { 1nat % z }
  else {
    let temp = mod_exp_helper(x, y / 2, z);
    let temp_squared = (temp * temp) % z;
    if y % 2 == 0 { temp_squared }
    else { (temp_squared * (x % z)) % z }
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): fix nat/int type conversion issues */
  let x = str2int(sx);
  let y = str2int(sy);
  let z = str2int(sz);
  
  proof {
    lemma_mod_exp_helper(x, y, z);
  }
  
  let result_nat = mod_exp_helper(x, y, z);
  
  // Convert nat to bit string representation
  ghost let mut remaining = result_nat;
  let mut result_seq = Seq::empty();
  
  while remaining > 0
    invariant
      remaining <= result_nat,
      str2int(result_seq) + remaining * exp_int(2, result_seq.len() as nat) == result_nat,
      valid_bit_string(result_seq),
    decreases remaining
  {
    if remaining % 2 == 0 {
      result_seq = result_seq.push('0');
    } else {
      result_seq = result_seq.push('1');
    }
    remaining = remaining / 2;
  }
  
  if result_seq.len() == 0 {
    result_seq = result_seq.push('0');
  }
  
  result_seq
}
// </vc-code>


}

fn main() {}