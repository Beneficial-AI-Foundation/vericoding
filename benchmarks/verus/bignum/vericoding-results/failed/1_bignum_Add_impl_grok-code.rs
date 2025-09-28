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
/* helper modified by LLM (iteration 9): add str2int_low and fix pow2 to take int */
spec fn pow2(i: int) -> nat
    decreases i when i > 0
{
    if i <= 0 { 1nat } else { 2nat * pow2(i - 1) }
}

spec fn str2int_low(s: Seq<char>, k: int) -> nat
    decreases k
{
    if k == 0 {0nat} else { if s[k-1] == '1' {1nat} else {0nat} + 2nat * str2int_low(s, k -1) }
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
    /* code modified by LLM (iteration 9): fix invariant to use str2int_low and adjust types */
    let max_len = s1.len().max(s2.len());
    let mut res: Vec<char> = Vec::new();
    let mut carry: usize = 0;
    let mut i: usize = 0;
    while i < max_len
        invariant
            i@ <= max_len@,
            res@.len() == i@,
            0 <= carry <= 2,
            str2int_low(res@, i@) + (carry as nat) * pow2(i@) == str2int_low(s1@, if i@ <= s1@.len() { i@ } else { s1@.len() }) + str2int_low(s2@, if i@ <= s2@.len() { i@ } else { s2@.len() })
        decreases max_len@ - i@
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        res.push(if sum % 2 == 0 { '0' } else { '1' });
        carry = sum / 2;
        i = i + 1;
    }
    if carry == 1 {
        res.push('1');
    }
    res
}
// </vc-code>


}

fn main() {}