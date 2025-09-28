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
/* helper modified by LLM (iteration 7): fixed nat literals to use proper syntax and type annotations */
spec fn int2str(n: nat, len: nat) -> Seq<char>
  decreases len
{
  if len == 0 {
    seq![]
  } else {
    int2str(n / 2, (len - 1) as nat).push(if n % 2 == 0 { '0' } else { '1' })
  }
}

proof fn lemma_int2str_valid(n: nat, len: nat)
  ensures valid_bit_string(int2str(n, len))
  decreases len
{
  if len == 0 {
  } else {
    lemma_int2str_valid(n / 2, (len - 1) as nat);
  }
}

fn mod_exp_helper(x: nat, y: nat, z: nat) -> (res: nat)
  requires z > 1
  ensures res == exp_int(x, y) % z
  decreases y
{
  if y == 0 {
    1
  } else {
    let half_exp = mod_exp_helper(x, y / 2, z);
    let squared = (half_exp * half_exp) % z;
    if y % 2 == 0 {
      squared
    } else {
      (squared * (x % z)) % z
    }
  }
}

exec fn from_seq(s: Seq<char>) -> (res: Vec<char>)
  ensures res@ == s
{
  let mut result = Vec::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      result@ == s.subrange(0, i as int)
  {
    result.push(s@[i as int]);
    i = i + 1;
  }
  result
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
  /* code modified by LLM (iteration 7): fixed compilation errors with proper type annotations and syntax */
  let x = str2int(sx@);
  let y = str2int(sy@);
  let z = str2int(sz@);
  
  let result_nat = mod_exp_helper(x, y, z);
  
  let result_len = sz@.len();
  let result_seq = int2str(result_nat, result_len);
  
  proof {
    lemma_int2str_valid(result_nat, result_len);
  }
  
  from_seq(result_seq)
}
// </vc-code>


}

fn main() {}