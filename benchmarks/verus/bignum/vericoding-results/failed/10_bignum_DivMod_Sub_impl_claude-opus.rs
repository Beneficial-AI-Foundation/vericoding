// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Remove sub_vec function and fix indexing in check_geq */
spec fn geq(s1: Seq<char>, s2: Seq<char>) -> bool
    recommends valid_bit_string(s1) && valid_bit_string(s2)
{
    str2int(s1) >= str2int(s2)
}

fn check_geq(s1: &Vec<char>, s2: &Vec<char>) -> (res: bool)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@)
    ensures
        res == (str2int(s1@) >= str2int(s2@))
{
    // Remove leading zeros for comparison
    let mut s1_start: usize = 0;
    while s1_start < s1.len() && s1[s1_start] == '0'
        invariant
            s1_start <= s1.len(),
            forall|j: int| 0 <= j < s1_start ==> s1@[j] == '0'
        decreases s1.len() - s1_start
    {
        s1_start = s1_start + 1;
    }
    
    let mut s2_start: usize = 0;
    while s2_start < s2.len() && s2[s2_start] == '0'
        invariant
            s2_start <= s2.len(),
            forall|j: int| 0 <= j < s2_start ==> s2@[j] == '0'
        decreases s2.len() - s2_start
    {
        s2_start = s2_start + 1;
    }
    
    let s1_len = s1.len() - s1_start;
    let s2_len = s2.len() - s2_start;
    
    if s1_len > s2_len {
        return true;
    } else if s1_len < s2_len {
        return false;
    }
    
    // Same length, compare bit by bit from most significant
    if s1_len == 0 {
        return true; // Both are zero
    }
    
    let mut i: usize = s1_start;
    while i < s1.len()
        invariant
            s1_start <= i,
            i <= s1.len(),
            s1_len == s2_len,
            forall|j: int| s1_start <= j < i ==> s1@[j] == s2@[s2_start + (j - s1_start)]
        decreases s1.len() - i
    {
        let idx2 = s2_start + (i - s1_start);
        if s1[i] == '1' && s2[idx2] == '0' {
            return true;
        } else if s1[i] == '0' && s2[idx2] == '1' {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fix indexing issue - use usize for executable indexing */
    let mut quotient = Vec::new();
    let mut remainder = dividend.clone();
    
    // Handle case where dividend < divisor
    if !check_geq(&remainder, &divisor) {
        quotient.push('0');
        proof {
            assert(str2int(quotient@) == 0);
            assert(str2int(remainder@) == str2int(dividend@));
            assert(str2int(dividend@) < str2int(divisor@));
            assert(str2int(dividend@) / str2int(divisor@) == 0);
            assert(str2int(dividend@) % str2int(divisor@) == str2int(dividend@));
        }
        return (quotient, remainder);
    }
    
    // Count bits for quotient
    let mut count: u64 = 0;
    
    while check_geq(&remainder, &divisor)
        invariant
            valid_bit_string(remainder@),
            valid_bit_string(divisor@),
            str2int(divisor@) > 0,
            str2int(remainder@) + count * str2int(divisor@) == str2int(dividend@),
            str2int(remainder@) < str2int(dividend@) || count == 0
        decreases str2int(remainder@)
    {
        // Call sub with Seq arguments and store result
        let sub_result = sub(remainder@, divisor@);
        
        // Convert result back to Vec
        let mut new_remainder = Vec::new();
        let mut i: usize = 0;
        while i < sub_result.len()
            invariant
                i <= sub_result.len(),
                new_remainder@.len() == i as int,
                forall|j: int| 0 <= j < i ==> new_remainder@[j] == sub_result[j]
            decreases sub_result.len() - i
        {
            new_remainder.push(sub_result[i as int]);
            i = i + 1;
        }
        
        remainder = new_remainder;
        count = count + 1;
        proof {
            assert(str2int(remainder@) < str2int(dividend@));
        }
    }
    
    // Convert count to binary representation
    if count == 0 {
        quotient.push('0');
    } else {
        let mut temp = count;
        let mut bits = Vec::new();
        while temp > 0
            invariant
                temp <= count
            decreases temp
        {
            if temp % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp = temp / 2;
        }
        
        // Reverse to get proper order
        let mut i: usize = bits.len();
        while i > 0
            invariant
                i <= bits.len(),
                quotient@.len() == bits.len() - i
            decreases i
        {
            i = i - 1;
            quotient.push(bits[i]);
        }
    }
    
    proof {
        assert(valid_bit_string(quotient@));
        assert(valid_bit_string(remainder@));
        assert(str2int(quotient@) == str2int(dividend@) / str2int(divisor@));
        assert(str2int(remainder@) == str2int(dividend@) % str2int(divisor@));
    }
    
    (quotient, remainder)
}
// </vc-code>


}

fn main() {}