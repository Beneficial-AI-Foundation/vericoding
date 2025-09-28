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
/* helper modified by LLM (iteration 10): fixed invariants to handle empty vector */
fn reverse_vec<T: Clone>(v: &mut Vec<T>) {
    let mut i = 0;
    let len = v.len();
    while i < len / 2
        invariant 
            v.len() == len,
            0 <= i <= len/2,
            len == 0 || 0 <= i < len,
            len == 0 || 0 <= len-1-i < len,
        decreases len/2 - i,
    {
        let j = len - 1 - i;
        let temp = v[i].clone();
        v[i] = v[j].clone();
        v[j] = temp;
        i += 1;
    }
}
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
/* code modified by LLM (iteration 10): added invariants and assertions for safe indexing and result validity */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };

    let mut borrow = 0;
    let mut result = Vec::new();

    let mut i = 0;
    while i < max_len
        invariant
            borrow == 0 || borrow == 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == '0' || result[j] == '1',
        decreases max_len - i,
    {
        let bit1 = if i < len1 {
            assert(0 <= len1 - 1 - i < len1);
            s1[len1 - 1 - i]
        } else {
            '0'
        };
        let bit2 = if i < len2 {
            assert(0 <= len2 - 1 - i < len2);
            s2[len2 - 1 - i]
        } else {
            '0'
        };

        let b1 = if bit1 == '1' { 1 } else { 0 };
        let b2 = if bit2 == '1' { 1 } else { 0 };

        let diff = b1 - b2 - borrow;
        if diff < 0 {
            borrow = 1;
            let current_bit = diff + 2;
            result.push(if current_bit == 1 { '1' } else { '0' });
        } else {
            borrow = 0;
            result.push(if diff == 1 { '1' } else { '0' });
        }
        i += 1;
    }

    assert(borrow == 0);
    reverse_vec(&mut result);
    assert(forall|j: int| 0 <= j < result.len() ==> result[j] == '0' || result[j] == '1');
    
    result
}
// </vc-code>


}

fn main() {}