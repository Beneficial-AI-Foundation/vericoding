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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    str2int(s1@) >= str2int(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) - str2int(s2@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Removed invalid 'int' suffixes from integer literals */
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    let len: usize = if len1 > len2 { len1 } else { len2 };
    let mut borrow: int = 0;
    let mut res: Vec<char> = Vec::new();
    for idx in 0..len {
        let current_idx = len - 1 - idx;
        let bit1: int = if current_idx < len1 && s1[current_idx] == '1' { 1 } else { 0 };
        let bit2: int = if current_idx < len2 && s2[current_idx] == '1' { 1 } else { 0 };
        let mut bit: int = bit1 - bit2 - borrow;
        if bit < 0 {
            bit += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        res.push(if bit == 1 { '1' } else { '0' });
    }
    res.reverse();
    // remove leading zeros
    let mut start: usize = 0;
    while start < res.len() && res[start] == '0'
        invariant
            start <= res.len(),
            borrow == 0 || borrow == 1,
        decreases res.len() - start
    {
        start += 1;
    }
    let mut result = Vec::new();
    if start == res.len() {
        result.push('0');
    } else {
        for j in start..res.len() {
            result.push(res[j]);
        }
    }
    result
}
// </vc-code>


}

fn main() {}