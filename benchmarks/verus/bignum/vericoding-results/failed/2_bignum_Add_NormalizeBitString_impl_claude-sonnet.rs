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
/* helper modified by LLM (iteration 10): fixed type annotations for integer literals */
spec fn bit_value(c: char) -> nat {
    if c == '1' { 1nat } else { 0nat }
}

spec fn add_bits_spec(b1: bool, b2: bool, carry_in: bool) -> (bool, bool) {
    let sum = (if b1 { 1nat } else { 0nat }) + (if b2 { 1nat } else { 0nat }) + (if carry_in { 1nat } else { 0nat });
    (sum % 2nat == 1nat, sum >= 2nat)
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
    /* code modified by LLM (iteration 10): fixed type annotations for integer literals */
    let norm_s1 = normalize_bit_string(s1@);
    let norm_s2 = normalize_bit_string(s2@);
    
    let mut result = Vec::new();
    let mut carry = false;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    let mut i = 0;
    while i < max_len || carry
        invariant
            valid_bit_string(result@),
            i <= max_len,
        decreases max_len + (if carry { 1usize } else { 0usize }) - i
    {
        let bit1 = if i < s1.len() { s1[s1.len() - 1 - i] == '1' } else { false };
        let bit2 = if i < s2.len() { s2[s2.len() - 1 - i] == '1' } else { false };
        
        let sum = (if bit1 { 1nat } else { 0nat }) + (if bit2 { 1nat } else { 0nat }) + (if carry { 1nat } else { 0nat });
        
        if sum % 2nat == 1nat {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum >= 2nat;
        i += 1;
    }
    
    result.reverse();
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>


}

fn main() {}