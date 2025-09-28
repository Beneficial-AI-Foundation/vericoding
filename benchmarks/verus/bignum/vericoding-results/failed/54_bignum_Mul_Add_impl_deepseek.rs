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
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 10): Fixed spec_pow2 with proper decreases clause */
spec fn spec_pow2(n: nat) -> nat 
  decreases n
{
  if n == 0 { 1nat } else { 2nat * spec_pow2((n - 1) as nat) }
}

proof fn lemma_str2int_additive(s1: Seq<char>, s2: Seq<char>)
  requires 
    valid_bit_string(s1),
    valid_bit_string(s2),
  ensures 
    str2int(s1.add(s2)) == str2int(s1) + str2int(s2),
  decreases s1.len() + s2.len()
{
  if s1.len() == 0 {
    assert(s1.add(s2) == s2);
  } else if s2.len() == 0 {
    assert(s1.add(s2) == s1);
  } else {
    let s1_last = s1[s1.len() - 1];
    let s1_prefix = s1.subrange(0, s1.len() - 1);
    let s2_last = s2[s2.len() - 1];
    let s2_prefix = s2.subrange(0, s2.len() - 1);
    
    lemma_str2int_additive(s1_prefix, s2);
    lemma_str2int_additive(s1, s2_prefix);
    lemma_str2int_additive(s1_prefix, s2_prefix);
    
    let combined = if s1_last == '1' && s2_last == '1' {
      2nat
    } else if s1_last == '1' || s2_last == '1' {
      1nat
    } else {
      0nat
    };
    
    assert(combined == (if s1_last == '1' {1nat} else {0nat}) + (if s2_last == '1' {1nat} else {0nat}));
  }
}

spec fn is_power_of_two(n: nat) -> bool {
  exists|k: nat| n == spec_pow2(k)
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
  requires valid_bit_string(s),
  ensures str2int(s) >= 0,
  decreases s.len()
{
  if s.len() > 0 {
    lemma_str2int_nonnegative(s.subrange(0, s.len() - 1));
  }
}

proof fn lemma_str2int_upper_bound(s: Seq<char>)
  requires valid_bit_string(s),
  ensures str2int(s) < spec_pow2(s.len() as nat),
  decreases s.len()
{
  if s.len() == 0 {
    assert(str2int(s) == 0);
  } else {
    let prefix = s.subrange(0, s.len() - 1);
    lemma_str2int_upper_bound(prefix);
    
    let last_digit = if s[s.len() - 1] == '1' {1nat} else {0nat};
    assert(str2int(s) == 2 * str2int(prefix) + last_digit);
    assert(str2int(prefix) < spec_pow2(prefix.len() as nat));
    assert(2 * str2int(prefix) + last_digit < 2 * spec_pow2(prefix.len() as nat) + 1);
    assert(2 * spec_pow2(prefix.len() as nat) + 1 <= spec_pow2(s.len() as nat));
  }
}

fn add_executable(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) + str2int(s2@),
{
  let mut result = Vec::new();
  let mut carry = false;
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  
  for i in 0..max_len {
    let bit1 = if i < s1.len() { s1[i] == '1' } else { false };
    let bit2 = if i < s2.len() { s2[i] == '1' } else { false };
    
    let sum = (bit1 as u8) + (bit2 as u8) + (carry as u8);
    carry = sum >= 2;
    let output_bit = if (sum % 2) == 1 { '1' } else { '0' };
    result.push(output_bit);
  }
  
  if carry {
    result.push('1');
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
{
    /* code modified by LLM (iteration 10): Using add_executable for multiplication */
    let mut result = Vec::new();
    let mut temp = Vec::new();
    
    for i in 0..s2.len() {
        if s2[i] == '1' {
            let mut shifted = s1.clone();
            for _ in 0..i {
                shifted.push('0');
            }
            
            temp = add_executable(shifted, temp);
        }
    }
    
    result = temp;
    result
}
// </vc-code>


}

fn main() {}