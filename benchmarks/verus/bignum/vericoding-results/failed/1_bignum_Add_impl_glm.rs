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
/* helper modified by LLM (iteration 5): fixed power function usage and simplified expression */
proof fn lemma_str2int_add(s1: Seq<char>, s2: Seq<char>, carry: nat)
    requires
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures
        str2int(s1) + str2int(s2) + carry ==
        if s1.len() == 0 {
            str2int(s2) + carry
        } else if s2.len() == 0 {
            str2int(s1) + carry
        } else {
            let last1: nat = if s1[s1.len() - 1] == '1' { 1nat } else { 0nat };
            let last2: nat = if s2[s2.len() - 1] == '1' { 1nat } else { 0nat };
            let sum = last1 + last2 + carry;
            let new_carry = sum / 2;
            let new_bit = if sum % 2 == 1 { '1' } else { '0' };
            2 * (str2int(s1.subrange(0, s1.len() - 1)) + str2int(s2.subrange(0, s2.len() - 1)) + new_carry) + (if new_bit == '1' { 1nat } else { 0nat })
        }
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
    } else if s2.len() == 0 {
    } else {
        let last1: nat = if s1[s1.len() - 1] == '1' { 1nat } else { 0nat };
        let last2: nat = if s2[s2.len() - 1] == '1' { 1nat } else { 0nat };
        let sum = last1 + last2 + carry;
        let new_carry = sum / 2;
        lemma_str2int_add(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), new_carry);
    }
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
    /* code modified by LLM (iteration 5): fixed power function and simplified invariant */
    let mut i = 0;
    let mut carry = 0;
    let mut res = Vec::new();
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            valid_bit_string(s1@) && valid_bit_string(s2@),
            valid_bit_string(res@),
            str2int(res@) + carry * pow_nat(2nat, i as nat) == str2int(s1@.subrange(0, i as int)) + str2int(s2@.subrange(0, i as int)),
            0 <= carry <= 1,
        decreases (if s1.len() > s2.len() { s1.len() } else { s2.len() } + 1 - i) as int, carry
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        res.push(new_bit);
        i += 1;
    }
    
    proof {
        lemma_str2int_add(s1@, s2@, 0);
    }
    
    res
}
// </vc-code>


}

fn main() {}