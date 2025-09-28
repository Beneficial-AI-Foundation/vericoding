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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed function signature syntax */
proof fn add_proof(s1: Seq<char>, s2: Seq<char>, carry: bool) -> (Seq<char>, bool)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() == s2.len(),
    carry ==> (str2int(s1) + str2int(s2) + 1 < pow2(s1.len() as nat)),
    !carry ==> (str2int(s1) + str2int(s2) < pow2(s1.len() as nat))
  ensures
    valid_bit_string(#[trigger] res),
    res.len() == s1.len(),
    str2int(res) + (if final_carry { pow2(s1.len() as nat) } else { 0 }) == str2int(s1) + str2int(s2) + (if carry { 1 } else { 0 })
  decreases s1.len()
{
  if s1.len() == 0 {
    (Seq::empty(), carry)
  } else {
    let last1 = s1[s1.len() - 1];
    let last2 = s2[s2.len() - 1];
    let bit1 = last1 == '1';
    let bit2 = last2 == '1';
    let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
    let new_bit = if sum % 2 == 1 { '1' } else { '0' };
    let new_carry = sum >= 2;
    
    let (prefix_res, final_carry_flag) = add_proof(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), new_carry);
    (prefix_res.push(new_bit), final_carry_flag)
  }
}

spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1nat } else { 2nat * pow2(n - 1) }
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed compilation error in function signature */
    let len = std::cmp::max(s1.len(), s2.len());
    let mut s1_padded = s1.clone();
    let mut s2_padded = s2.clone();
    
    while s1_padded.len() < len {
        s1_padded.push('0');
    }
    while s2_padded.len() < len {
        s2_padded.push('0');
    }
    
    let mut res = Vec::new();
    let mut carry = false;
    let mut i = 0;
    
    while i < len
        invariant
            valid_bit_string(res@),
            str2int(res@) + (if carry { pow2(i as nat) } else { 0 }) == 
                str2int(s1_padded@.subrange(0, i)) + str2int(s2_padded@.subrange(0, i)),
            i <= len
        decreases len - i
    {
        let bit1 = if i < s1_padded.len() { s1_padded[i] == '1' } else { false };
        let bit2 = if i < s2_padded.len() { s2_padded[i] == '1' } else { false };
        let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum >= 2;
        res.push(new_bit);
        i += 1;
    }
    
    let final_carry = carry;
    
    if final_carry {
        res.push('1');
    }
    
    res
}
// </vc-code>


}

fn main() {}