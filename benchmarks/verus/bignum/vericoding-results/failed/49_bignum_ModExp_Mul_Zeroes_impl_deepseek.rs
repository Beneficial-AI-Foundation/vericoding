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
/* helper modified by LLM (iteration 10): Fix type conversion by using proper usize instead of nat in executable code and add helper for exponentiation */
proof fn lemma_exp_recursive(x: nat, y: nat) 
  ensures 
    exp_int(x, y) == if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
  decreases y
{
  if y > 0 {
    lemma_exp_recursive(x, (y - 1) as nat);
  }
}

proof fn lemma_square_exp(x: nat, y: nat)
  ensures 
    exp_int(x * x, y / 2) == exp_int(x, 2 * (y / 2))
  decreases y
{
  if y > 0 {
    lemma_square_exp(x, (y - 1) as nat);
  }
}

fn vec_from_seq(s: Seq<char>) -> Vec<char> {
  let mut v = Vec::new();
  let mut i: usize = 0;
  let len: usize = s.len() as usize;
  while i < len
    invariant
      0 <= i <= len,
      v@ == s.subrange(0, i as int)
  {
    v.push(s[i as int]);
    i += 1;
  }
  v
}

fn zeros_usize(n: usize) -> Vec<char> {
  vec_from_seq(zeros(n as nat))
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
    /* code modified by LLM (iteration 10): Fixed executable implementation using proper usize instead of nat */
    let mut result = Vec::new();
    let mut base = sx;
    let mut exponent = sy;
    let modulus = sz;
    
    result.push('1');
    
    while exponent.len() > 0 {
        let last_char = exponent.last().unwrap();
        if *last_char == '1' {
            result = mul(result@, base@);
            result = mul(result@, modulus@);
        }
        base = mul(base@, base@);
        base = mul(base@, modulus@);
        
        let mut truncated = exponent.clone();
        truncated.pop();
        exponent = truncated;
    }
    
    result
}
// </vc-code>


}

fn main() {}