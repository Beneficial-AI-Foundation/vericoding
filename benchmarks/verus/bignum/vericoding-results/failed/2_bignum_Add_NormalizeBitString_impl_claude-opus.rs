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
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): Fixed Seq indexing - use usize directly, not nat */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j],
        decreases s.len() - i
    {
        v.push(s[i]);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): Implementation unchanged from iteration 6 */
    let n1 = normalize_bit_string(s1@);
    let n2 = normalize_bit_string(s2@);
    
    let n1_vec = seq_to_vec(n1);
    let n2_vec = seq_to_vec(n2);
    
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut i: usize = 0;
    let max_len = if n1_vec.len() > n2_vec.len() { n1_vec.len() } else { n2_vec.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len + 1,
            carry == 0 || carry == 1,
            valid_bit_string(result@),
            n1_vec@ == n1,
            n2_vec@ == n2,
        decreases max_len + 1 - i
    {
        let bit1 = if i < n1_vec.len() { 
            if n1_vec[n1_vec.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let bit2 = if i < n2_vec.len() { 
            if n2_vec[n2_vec.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        let bit = sum % 2;
        
        result.insert(0, if bit == 1 { '1' } else { '0' });
        i = i + 1;
        
        if i >= max_len && carry == 0 {
            break;
        }
    }
    
    let normalized = normalize_bit_string(result@);
    let final_result = seq_to_vec(normalized);
    
    proof {
        assert(str2int(final_result@) == str2int(s1@) + str2int(s2@));
    }
    
    final_result
}
// </vc-code>


}

fn main() {}