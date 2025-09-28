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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatches with nat/usize conversions and sequence indexing */

spec fn get_bit_value(s: Seq<char>, i: nat) -> nat {
    if i < s.len() && s[i as int] == '1' { 1nat } else { 0nat }
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j]
        decreases s.len() - i
    {
        v.push(s[i as int]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@) &&
    str2int(s1@) >= str2int(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) - str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type mismatches between nat/usize and sequence indexing */
    let normalized_s1 = normalize_bit_string(s1@);
    let normalized_s2 = normalize_bit_string(s2@);
    
    if normalized_s1.len() < normalized_s2.len() {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    let mut borrow = 0;
    let max_len = if normalized_s1.len() > normalized_s2.len() { normalized_s1.len() } else { normalized_s2.len() };
    
    let mut i: usize = 0;
    while i < max_len as usize
        invariant
            i <= max_len,
            valid_bit_string(result@),
            borrow == 0 || borrow == 1
        decreases max_len - i
    {
        let idx1 = (normalized_s1.len() - 1) as int - (i as int);
        let idx2 = (normalized_s2.len() - 1) as int - (i as int);
        
        let bit1 = if (i as nat) < normalized_s1.len() {
            if normalized_s1[idx1] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let bit2 = if (i as nat) < normalized_s2.len() {
            if normalized_s2[idx2] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let diff = bit1 - bit2 - borrow;
        
        if diff >= 0 {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.push('1');
            borrow = 1;
        }
        
        i += 1;
    }
    
    result.reverse();
    
    let normalized_result = normalize_bit_string(result@);
    seq_to_vec(normalized_result)
}
// </vc-code>


}

fn main() {}