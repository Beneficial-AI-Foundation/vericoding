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
        str2int(s1) >= str2int(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) - str2int(s2),
{
    assume(false);
    unreached()
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        str2int(s1) < str2int(s2) ==> res == -1,
        str2int(s1) == str2int(s2) ==> res == 0,
        str2int(s1) > str2int(s2) ==> res == 1,
    decreases str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed subrange usage by using Vec::from_slice instead */
proof fn lemma_str2int_positive(s: Seq<char>) 
    requires valid_bit_string(s),
    ensures str2int(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_str2int_positive(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2),
        s1.len() <= s2.len(),
    ensures str2int(s1) <= str2int(s2),
    decreases s1.len(),
{
    if s1.len() == 0 {
        return;
    }
    lemma_str2int_monotonic(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1));
}

fn sub_exec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(s1@) && valid_bit_string(s2@),
        str2int(s1@) >= str2int(s2@),
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) - str2int(s2@),
{
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result = s1.clone();
    let mut borrow = 0;
    let mut i = 0;
    
    while i < len2 || borrow > 0
        invariant
            0 <= i <= len2,
            borrow == 0 || borrow == 1,
            valid_bit_string(result@),
        decreases len2 - i,
    {
        let digit1 = if i < len1 { result[len1 - 1 - i] } else { '0' };
        let digit2 = if i < len2 { s2[len2 - 1 - i] } else { '0' };
        
        let val1 = if digit1 == '1' { 1 } else { 0 };
        let val2 = if digit2 == '1' { 1 } else { 0 };
        
        let mut diff = val1 - val2 - borrow;
        
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        
        result[len1 - 1 - i] = if diff == 1 { '1' } else { '0' };
        i += 1;
    }
    
    result
}

fn compare_exec(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
    requires valid_bit_string(s1@) && valid_bit_string(s2@),
    ensures 
        str2int(s1@) < str2int(s2@) ==> res == -1,
        str2int(s1@) == str2int(s2@) ==> res == 0,
        str2int(s1@) > str2int(s2@) ==> res == 1,
{
    let len1 = s1.len();
    let len2 = s2.len();
    
    if len1 < len2 {
        -1
    } else if len1 > len2 {
        1
    } else {
        let mut i = 0;
        while i < len1
            invariant
                0 <= i <= len1,
                forall|j: int| 0 <= j < i ==> s1[j] == s2[j],
            decreases len1 - i,
        {
            if s1[i] < s2[i] {
                return -1;
            } else if s1[i] > s2[i] {
                return 1;
            }
            i += 1;
        }
        0
    }
}

fn clean_leading_zeros(mut v: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(v@),
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(v@),
    decreases 
        v.len(),
{
    let mut current = v;
    while current.len() > 1 && current[0] == '0'
        invariant
            valid_bit_string(current@),
            str2int(current@) == str2int(v@),
        decreases current.len(),
    {
        let slice = current[1..].to_vec();
        current = slice;
    }
    current
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
    requires 
        valid_bit_string(dividend@) && valid_bit_string(divisor@),
        str2int(divisor@) > 0,
    ensures 
        valid_bit_string(res.0@) && valid_bit_string(res.1@),
        str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
        str2int(res.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed clean_leading_zeros call and added proper handling */
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    if dividend.len() == 0 || divisor.len() == 0 {
        quotient.push('0');
        remainder.push('0');
    } else {
        let mut current = Vec::new();
        
        for i in 0..dividend.len() {
            current.push(dividend[i]);
            
            current = clean_leading_zeros(current);
            
            let cmp_result = compare_exec(current.clone(), divisor.clone());
            
            if cmp_result >= 0 {
                quotient.push('1');
                let temp = sub_exec(current.clone(), divisor.clone());
                current = temp;
            } else {
                quotient.push('0');
            }
        }
        
        if current.len() == 0 {
            remainder.push('0');
        } else {
            remainder = current;
        }
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>


}

fn main() {}