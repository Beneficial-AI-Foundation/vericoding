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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
  decreases str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatches in indexing */
proof fn lemma_str2int_empty()
    ensures str2int(Seq::<char>::empty()) == 0nat
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s.push('0')) == 2nat * str2int(s)
    decreases s.len()
{
    assert(s.push('0').subrange(0, s.push('0').len() - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s.push('1')) == 2nat * str2int(s) + 1nat
    decreases s.len()
{
    assert(s.push('1').subrange(0, s.push('1').len() - 1) == s);
}

fn compare_vecs(v1: &Vec<char>, v2: &Vec<char>) -> (res: i32)
    requires
        valid_bit_string(v1@),
        valid_bit_string(v2@)
    ensures
        str2int(v1@) < str2int(v2@) ==> res == -1,
        str2int(v1@) == str2int(v2@) ==> res == 0,
        str2int(v1@) > str2int(v2@) ==> res == 1
{
    // First compare lengths (leading zeros removed)
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    // Skip leading zeros in v1
    while i1 < v1.len() && v1[i1] == '0'
        invariant
            0 <= i1 <= v1.len()
        decreases v1.len() - i1
    {
        i1 = i1 + 1;
    }
    
    // Skip leading zeros in v2
    while i2 < v2.len() && v2[i2] == '0'
        invariant
            0 <= i2 <= v2.len()
        decreases v2.len() - i2
    {
        i2 = i2 + 1;
    }
    
    let len1 = v1.len() - i1;
    let len2 = v2.len() - i2;
    
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    }
    
    // Same length, compare digit by digit
    let mut j: usize = 0;
    while j < len1
        invariant
            0 <= j <= len1,
            len1 == len2,
            i1 + len1 == v1.len(),
            i2 + len2 == v2.len(),
            i1 + j <= v1.len(),
            i2 + j <= v2.len()
        decreases len1 - j
    {
        let idx1 = i1 + j;
        let idx2 = i2 + j;
        assert(idx1 < v1.len());
        assert(idx2 < v2.len());
        
        let d1 = v1[idx1];
        let d2 = v2[idx2];
        
        if d1 == '0' && d2 == '1' {
            return -1;
        } else if d1 == '1' && d2 == '0' {
            return 1;
        }
        
        j = j + 1;
    }
    
    0
}

fn binary_subtract(minuend: &Vec<char>, subtrahend: &Vec<char>) -> (result: Vec<char>)
    requires
        valid_bit_string(minuend@),
        valid_bit_string(subtrahend@),
        str2int(minuend@) >= str2int(subtrahend@)
    ensures
        valid_bit_string(result@),
        str2int(result@) == str2int(minuend@) - str2int(subtrahend@)
{
    let mut result = Vec::new();
    let mut borrow = 0u8;
    let mut i: usize = 0;
    
    let max_len = if minuend.len() >= subtrahend.len() { minuend.len() } else { subtrahend.len() };
    
    while i < max_len || borrow > 0
        invariant
            0 <= i <= max_len + 1,
            borrow <= 1,
            valid_bit_string(result@),
            result.len() == i
        decreases (max_len + 2) - i
    {
        let m_digit = if i < minuend.len() {
            if minuend[minuend.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let s_digit = if i < subtrahend.len() {
            if subtrahend[subtrahend.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let diff = if m_digit >= s_digit + borrow {
            let res = m_digit - s_digit - borrow;
            borrow = 0;
            res
        } else {
            let res = m_digit + 2 - s_digit - borrow;
            borrow = 1;
            res
        };
        
        result.insert(0, if diff == 1 { '1' } else { '0' });
        i = i + 1;
    }
    
    // Remove leading zeros
    while result.len() > 1 && result[0] == '0'
        invariant
            result.len() >= 1,
            valid_bit_string(result@)
        decreases result.len()
    {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(res.0@) && valid_bit_string(res.1@),
    str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(res.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type mismatches in assertions */
    let mut quotient = Vec::new();
    let mut current = Vec::new();
    
    let mut j: usize = 0;
    while j < dividend.len()
        invariant
            0 <= j <= dividend.len(),
            valid_bit_string(quotient@),
            valid_bit_string(current@),
            quotient.len() == j,
            valid_bit_string(dividend@),
            valid_bit_string(divisor@)
        decreases dividend.len() - j
    {
        // Append next bit from dividend
        proof {
            assert(dividend@[j as int] == '0' || dividend@[j as int] == '1');
            assert(forall|k: int| 0 <= k < current.len() ==> current@[k] == '0' || current@[k] == '1');
        }
        current.push(dividend[j]);
        
        proof {
            assert(forall|k: int| 0 <= k < current.len() - 1 ==> current@[k] == '0' || current@[k] == '1');
            assert(current@[current.len() - 1] == dividend@[j as int]);
            assert(current@[current.len() - 1] == '0' || current@[current.len() - 1] == '1');
            assert(valid_bit_string(current@));
        }
        
        // Remove leading zeros from current  
        while current.len() > 1 && current[0] == '0'
            invariant
                current.len() >= 1,
                valid_bit_string(current@)
            decreases current.len()
        {
            current.remove(0);
        }
        
        // Compare current with divisor
        let cmp = compare_vecs(&current, &divisor);
        
        if cmp >= 0 {
            quotient.push('1');
            current = binary_subtract(&current, &divisor);
        } else {
            quotient.push('0');
        }
        
        j = j + 1;
    }
    
    // Remove leading zeros from quotient
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    while quotient.len() > 1 && quotient[0] == '0'
        invariant
            quotient.len() >= 1,
            valid_bit_string(quotient@)
        decreases quotient.len()
    {
        quotient.remove(0);
    }
    
    if current.len() == 0 {
        current.push('0');
    }
    
    (quotient, current)
}
// </vc-code>


}

fn main() {}