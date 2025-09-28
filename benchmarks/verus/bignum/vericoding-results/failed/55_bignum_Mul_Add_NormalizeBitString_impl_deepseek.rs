// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
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
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix compilation error and ensure proper syntax */
proof fn lemma_str2int_zero(s: Seq<char>) 
  decreases s.len()
  requires 
    valid_bit_string(s)
  ensures 
    str2int(s) == 0 ==> s == Seq::<char>::empty()
{
  if s.len() > 0 {
    let last_char = s[s.len() - 1];
    assert(last_char == '0' || last_char == '1');
    let prefix = s.subrange(0, s.len() - 1);
    lemma_str2int_zero(prefix);
  }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2) && s1 =~= s2
  ensures 
    str2int(s1) <= str2int(s2)
{
  if s1.len() > 0 && s2.len() > 0 {
    let s1_prefix = s1.subrange(0, s1.len() - 1);
    let s2_prefix = s2.subrange(0, s2.len() - 1);
    lemma_str2int_monotonic(s1_prefix, s2_prefix);
  }
}

spec fn binary_multiply(a: nat, b: nat) -> nat {
  if b == 0 {
    0nat
  } else if b % 2 == 0 {
    2nat * binary_multiply(a, b / 2)
  } else {
    2nat * binary_multiply(a, b / 2) + a
  }
}

proof fn lemma_binary_multiply_correct(a: nat, b: nat) 
  ensures 
    binary_multiply(a, b) == a * b
{
  if b > 0 {
    lemma_binary_multiply_correct(a, b / 2);
  }
}

fn shift_left(s: Vec<char>, n: usize) -> (res: Vec<char>)
  requires 
    valid_bit_string(s@)
  ensures 
    valid_bit_string(res@) && str2int(res@) == str2int(s@) * (pow(2, n as nat))
{
  let mut result = s.clone();
  let mut i: usize = 0;
  while i < n
    invariant
      i <= n,
      valid_bit_string(result@),
      str2int(result@) == str2int(s@) * (pow(2, i as nat))
  {
    result.push('0');
    i = i + 1;
  }
  result
}

fn binary_add_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) && str2int(res@) == str2int(s1@) + str2int(s2@)
{
  let mut result: Vec<char> = Vec::new();
  let mut carry = '0';
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  
  let mut i = 0;
  while i < max_len || carry == '1'
    invariant
      i <= max_len + 1,
      valid_bit_string(result@),
      str2int(result@) + (if carry == '1' { 1nat } else { 0nat }) * pow(2, i as nat) == 
        str2int(s1@.subrange(0, i as int)) + str2int(s2@.subrange(0, i as int))
  {
    let bit1 = if i < s1.len() { s1[i] } else { '0' };
    let bit2 = if i < s2.len() { s2[i] } else { '0' };
    
    let sum = match (bit1, bit2, carry) {
      ('0', '0', '0') => ('0', '0'),
      ('0', '0', '1') => ('1', '0'),
      ('0', '1', '0') => ('1', '0'),
      ('0', '1', '1') => ('0', '1'),
      ('1', '0', '0') => ('1', '0'),
      ('1', '0', '1') => ('0', '1'),
      ('1', '1', '0') => ('0', '1'),
      ('1', '1', '1') => ('1', '1'),
      _ => ('0', '0'),
    };
    
    result.push(sum.0);
    carry = sum.1;
    i = i + 1;
  }
  
  result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): fix compilation error and ensure proper syntax */
{
  if s2.len() == 0 {
    return vec!['0'];
  }
  
  let mut result = vec!['0'];
  
  let mut i = 0;
  while i < s2.len()
    invariant
      i <= s2.len(),
      valid_bit_string(result@),
      str2int(result@) == str2int(s1@) * str2int(s2@.subrange(0, i as int))
  {
    if s2[i] == '1' {
      let shift_amount = s2.len() - i - 1;
      let shifted = shift_left(s1.clone(), shift_amount);
      result = binary_add_bit_strings(result, shifted);
    }
    i = i + 1;
  }
  
  result
}
// </vc-code>


}

fn main() {}