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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
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
/* helper modified by LLM (iteration 10): fixed executable function to use usize instead of int for indexing */
spec fn mod_operation(a: nat, m: nat) -> nat
  requires m > 1
{
  a % m
}

proof fn mod_exp_properties(x: nat, y: nat, m: nat)
  requires m > 1
  ensures y == 0 ==> exp_int(x, y) % m == 1nat % m
{
}

proof fn exp_zero_lemma(x: nat)
  ensures exp_int(x, 0nat) == 1nat
{
}

proof fn mod_mul_lemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
  requires valid_bit_string(s)
  ensures v@ == s && valid_bit_string(v@)
{
  let mut v = Vec::new();
  let mut i: usize = 0;
  while i < s.len()
    invariant
      0 <= i <= s.len(),
      v@ == s.subrange(0, i as int),
      valid_bit_string(v@)
  {
    v.push(s[i as int]);
    i = i + 1;
  }
  v
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): simplified implementation without complex type conversions */
  if sy.len() == 0 {
    return vec!['1'];
  }
  
  if str2int(sy@) == 0 {
    return vec!['1'];
  }
  
  let mut result = vec!['1'];
  let mut base = sx.clone();
  let mut exp = sy.clone();
  
  while exp.len() > 0 && str2int(exp@) > 0
    invariant
      valid_bit_string(result@),
      valid_bit_string(base@),
      valid_bit_string(exp@),
      str2int(result@) < str2int(sz@)
  {
    if exp[exp.len() - 1] == '1' {
      result = seq_to_vec(mul(result@, base@));
    }
    base = seq_to_vec(mul(base@, base@));
    exp.pop();
  }
  
  result
}
// </vc-code>


}

fn main() {}