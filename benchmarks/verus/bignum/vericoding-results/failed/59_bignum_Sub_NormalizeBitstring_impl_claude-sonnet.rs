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
/* helper modified by LLM (iteration 10): helper function to reverse Vec with fixed bounds and invariants */
fn reverse_vec(mut v: Vec<char>) -> (res: Vec<char>)
    ensures res@.len() == v@.len(),
            forall|i: int| 0 <= i < v@.len() ==> res@[i] == v@[v@.len() - 1 - i],
            valid_bit_string(v@) ==> valid_bit_string(res@)
{
    let mut result = Vec::new();
    let len = v.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == v@[len - 1 - j],
            valid_bit_string(v@) ==> valid_bit_string(result@),
            len == v@.len()
        decreases len - i
    {
        assert(i < len);
        assert(len - 1 - i >= 0 && len - 1 - i < len);
        proof {
            if valid_bit_string(v@) {
                assert(v@[len - 1 - i] == '0' || v@[len - 1 - i] == '1');
            }
        }
        result.push(v[len - 1 - i]);
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 10): fix type errors with nat/int conversions and usize/int indexing */
    if str2int(s2@) == 0nat {
        return s1;
    }
    
    let mut result = Vec::new();
    let mut borrow = 0;
    let mut i = s1.len();
    let mut j = s2.len();
    
    while i > 0 || j > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            borrow == 0 || borrow == 1,
            valid_bit_string(result@)
        decreases i + j
    {
        let digit1 = if i > 0 { if s1[i - 1] == '1' { 1 } else { 0 } } else { 0 };
        let digit2 = if j > 0 { if s2[j - 1] == '1' { 1 } else { 0 } } else { 0 };
        
        let temp = digit1 - digit2 - borrow;
        
        if temp >= 0 {
            result.push(if temp == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.push('1');
            borrow = 1;
        }
        
        if i > 0 { i = i - 1; }
        if j > 0 { j = j - 1; }
    }
    
    result = reverse_vec(result);
    
    // Remove leading zeros
    let mut start_idx = 0;
    while start_idx < result.len() && result[start_idx] == '0'
        invariant
            0 <= start_idx <= result.len(),
            valid_bit_string(result@)
        decreases result.len() - start_idx
    {
        start_idx = start_idx + 1;
    }
    
    if start_idx == result.len() {
        vec!['0']
    } else {
        let mut normalized = Vec::new();
        let mut k = start_idx;
        while k < result.len()
            invariant
                start_idx <= k <= result.len(),
                normalized@.len() == k - start_idx,
                valid_bit_string(normalized@),
                start_idx < result.len()
            decreases result.len() - k
        {
            proof {
                assert(result@[k as int] == '0' || result@[k as int] == '1');
            }
            normalized.push(result[k]);
            k = k + 1;
        }
        normalized
    }
}
// </vc-code>


}

fn main() {}