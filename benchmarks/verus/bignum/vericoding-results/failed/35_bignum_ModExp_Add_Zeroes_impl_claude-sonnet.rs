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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix ghost type usage and type mismatches */
fn vec_to_seq<T: Copy>(v: Vec<T>) -> (s: Seq<T>)
  ensures s == v@
{
  v@
}

fn seq_to_vec<T: Copy>(s: Seq<T>) -> (v: Vec<T>)
  ensures v@ == s
{
  let mut result = Vec::new();
  let mut i: usize = 0;
  while i < s.len() as usize
    invariant
      0 <= i <= s.len(),
      result@ == s.subrange(0, i as int)
  {
    result.push(s[i as int]);
    i = i + 1;
  }
  result
}

fn half_exp(exp: Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(exp@), exp@.len() > 0
  ensures valid_bit_string(res@),
          str2int(res@) == str2int(exp@) / 2
{
  let mut result = exp.clone();
  if result.len() > 0 {
    result.pop();
  }
  if result.len() == 0 {
    result.push('0');
  }
  result
}

fn mod_multiply(a: Vec<char>, b: Vec<char>, m: Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(a@), valid_bit_string(b@), valid_bit_string(m@),
           str2int(m@) > 1
  ensures valid_bit_string(res@),
          str2int(res@) == (str2int(a@) * str2int(b@)) % str2int(m@)
{
  let a_seq = a@;
  let b_seq = b@;
  
  let product_seq = add(a_seq, b_seq);
  let result_seq = add(product_seq, zeros(0));
  
  seq_to_vec(result_seq)
}

proof fn lemma_str2int_subrange(s: Seq<char>)
  requires valid_bit_string(s), s.len() > 0
  ensures str2int(s) == 2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_exp_base_cases(x: nat, y: nat)
  ensures y == 0 ==> exp_int(x, y) == 1,
          y == 1 ==> exp_int(x, y) == x
{
}

proof fn lemma_mod_properties(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a % m + b % m) % m == (a + b) % m,
          (a % m * b % m) % m == (a * b) % m
{
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): fix type mismatches between usize and nat */
  let mut result = vec!['1'];
  let mut base = sx.clone();
  let mut exp = sy.clone();
  
  if sy@.len() == 1nat && sy[0] == '0' {
    return vec!['1'];
  }
  
  result = vec!['1'];
  
  while exp@.len() > 0nat && !all_zero(exp@)
    invariant
      valid_bit_string(result@),
      valid_bit_string(base@),
      valid_bit_string(exp@),
      str2int(sz@) > 1
  {
    if exp.len() > 0 && exp[exp.len() - 1] == '1' {
      result = mod_multiply(result, base.clone(), sz.clone());
    }
    
    base = mod_multiply(base.clone(), base.clone(), sz.clone());
    exp = half_exp(exp);
  }
  
  result
}
// </vc-code>


}

fn main() {}