// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): implement proper addition algorithm for bit strings */
fn add_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@),
    valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@)
{
  if s1.len() == 0 {
    return s2;
  }
  if s2.len() == 0 {
    return s1;
  }
  
  let mut result = Vec::new();
  let mut carry = false;
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  
  let mut i: usize = 0;
  while i < max_len
    invariant
      i <= max_len,
      valid_bit_string(result@)
    decreases max_len - i
  {
    let bit1_pos = if s1.len() > i { s1.len() - 1 - i } else { s1.len() };
    let bit2_pos = if s2.len() > i { s2.len() - 1 - i } else { s2.len() };
    
    let bit1 = if bit1_pos < s1.len() { s1[bit1_pos] == '1' } else { false };
    let bit2 = if bit2_pos < s2.len() { s2[bit2_pos] == '1' } else { false };
    
    let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
    
    result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
    carry = sum >= 2;
    
    i += 1;
  }
  
  if carry {
    result.insert(0, '1');
  }
  
  if result.len() == 0 {
    result.push('0');
  }
  
  result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fix loop invariants using invariant_except_break for early termination */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    // Check for all zeros using while loops
    let s1_all_zero = {
        let mut all_zero = true;
        let mut j: usize = 0;
        while j < s1.len()
            invariant_except_break
                all_zero ==> (forall|k: int| 0 <= k < j ==> s1[k] == '0'),
                j <= s1.len()
            decreases s1.len() - j
        {
            if s1[j] == '1' {
                all_zero = false;
                break;
            }
            j += 1;
        }
        all_zero
    };
    
    let s2_all_zero = {
        let mut all_zero = true;
        let mut j: usize = 0;
        while j < s2.len()
            invariant_except_break
                all_zero ==> (forall|k: int| 0 <= k < j ==> s2[k] == '0'),
                j <= s2.len()
            decreases s2.len() - j
        {
            if s2[j] == '1' {
                all_zero = false;
                break;
            }
            j += 1;
        }
        all_zero
    };
    
    if s1_all_zero || s2_all_zero {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    
    let mut i: usize = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            valid_bit_string(result@)
        decreases s2.len() - i
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted_s1 = s1.clone();
            let mut j: usize = 0;
            while j < i
                invariant
                    j <= i,
                    valid_bit_string(shifted_s1@),
                    shifted_s1.len() == s1.len() + j
                decreases i - j
            {
                shifted_s1.push('0');
                j += 1;
            }
            
            result = add_bit_strings(result, shifted_s1);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}