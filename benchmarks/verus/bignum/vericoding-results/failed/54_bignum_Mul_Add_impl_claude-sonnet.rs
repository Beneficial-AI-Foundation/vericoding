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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed seq_to_vec conversion function */
proof fn lemma_str2int_empty()
    ensures str2int(seq![]) == 0nat
{
    // str2int(seq![]) == 0nat by definition
}

proof fn lemma_empty_string_zero(s: Seq<char>)
    requires s.len() == 0
    ensures str2int(s) == 0nat
{
    // Empty string has str2int value of 0 by definition
    assert(s =~= seq![]);
    lemma_str2int_empty();
}

proof fn lemma_str2int_single_zero()
    ensures str2int(seq!['0']) == 0nat
{
    // str2int(seq!['0']) = 2 * str2int(seq![]) + 0 = 2 * 0 + 0 = 0
    lemma_str2int_empty();
    assert(seq!['0'].len() == 1);
    assert(seq!['0'][0] == '0');
    // By definition of str2int
    assert(str2int(seq!['0']) == 2nat * str2int(seq!['0'].subrange(0, 0)) + (if '0' == '1' { 1nat } else { 0nat }));
    assert(seq!['0'].subrange(0, 0) =~= seq![]);
    assert(str2int(seq!['0']) == 2nat * str2int(seq![]) + 0nat);
    assert(str2int(seq![]) == 0nat);
    assert(str2int(seq!['0']) == 0nat);
}

proof fn lemma_str2int_single_one()
    ensures str2int(seq!['1']) == 1nat
{
    // str2int(seq!['1']) = 2 * str2int(seq![]) + 1 = 2 * 0 + 1 = 1
    lemma_str2int_empty();
    assert(seq!['1'].len() == 1);
    assert(seq!['1'][0] == '1');
    // By definition of str2int
    assert(str2int(seq!['1']) == 2nat * str2int(seq!['1'].subrange(0, 0)) + (if '1' == '1' { 1nat } else { 0nat }));
    assert(seq!['1'].subrange(0, 0) =~= seq![]);
    assert(str2int(seq!['1']) == 2nat * str2int(seq![]) + 1nat);
    assert(str2int(seq![]) == 0nat);
    assert(str2int(seq!['1']) == 1nat);
}

proof fn lemma_valid_bit_string_empty()
    ensures valid_bit_string(seq![])
{
    // vacuously true
}

proof fn lemma_valid_bit_string_zero()
    ensures valid_bit_string(seq!['0'])
{
    // '0' is a valid bit character
}

proof fn lemma_valid_bit_string_one()
    ensures valid_bit_string(seq!['1'])
{
    // '1' is a valid bit character
}

proof fn lemma_multiplication_zero(a: nat)
    ensures a * 0nat == 0nat, 0nat * a == 0nat
{
    // multiplication by zero properties
}

proof fn lemma_multiplication_one(a: nat)
    ensures a * 1nat == a, 1nat * a == a
{
    // multiplication by one properties
}

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires valid_bit_string(s), bit == '0' || bit == '1'
    ensures str2int(s.push(bit)) == 2nat * str2int(s) + (if bit == '1' { 1nat } else { 0nat })
{
    let extended = s.push(bit);
    assert(extended.len() == s.len() + 1);
    assert(extended[extended.len() - 1] == bit);
    assert(extended.subrange(0, extended.len() - 1) =~= s);
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures
        valid_bit_string(res@),
        res@ == s
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            valid_bit_string(result@),
            valid_bit_string(s),
            forall|j: int| 0 <= j < i ==> result[j] == s[j]
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

fn binary_multiply_by_char(s: Vec<char>, multiplier: char) -> (res: Vec<char>)
    requires
        valid_bit_string(s@),
        multiplier == '0' || multiplier == '1'
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(s@) * (if multiplier == '1' { 1nat } else { 0nat })
{
    if multiplier == '0' {
        proof {
            lemma_multiplication_zero(str2int(s@));
            lemma_str2int_single_zero();
            lemma_valid_bit_string_zero();
        }
        let mut result = Vec::new();
        result.push('0');
        return result;
    } else {
        proof {
            lemma_multiplication_one(str2int(s@));
        }
        return s;
    }
}

fn shift_left(s: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s@)
    ensures
        valid_bit_string(res@),
        str2int(res@) == 2nat * str2int(s@)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            valid_bit_string(result@),
            valid_bit_string(s@),
            forall|j: int| 0 <= j < i ==> result[j] == s[j]
    {
        result.push(s[i]);
        i += 1;
    }
    result.push('0');
    
    proof {
        let original = s@;
        let shifted = result@;
        assert(shifted.len() == original.len() + 1);
        assert(shifted[shifted.len() - 1] == '0');
        assert(shifted.subrange(0, shifted.len() - 1) =~= original);
        lemma_str2int_append_bit(original, '0');
        assert(str2int(shifted) == 2nat * str2int(original) + 0nat);
        assert(str2int(shifted) == 2nat * str2int(original));
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use seq_to_vec to convert Seq to Vec */
    
    // Handle empty inputs
    if s1.len() == 0 || s2.len() == 0 {
        proof {
            if s1.len() == 0 {
                lemma_empty_string_zero(s1@);
                lemma_multiplication_zero(str2int(s2@));
            } else {
                lemma_empty_string_zero(s2@);
                lemma_multiplication_zero(str2int(s1@));
            }
            lemma_str2int_single_zero();
            lemma_valid_bit_string_zero();
        }
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    // Handle multiplication by zero
    if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
        proof {
            lemma_str2int_single_zero();
            lemma_multiplication_zero(if s1.len() == 1 && s1[0] == '0' { str2int(s2@) } else { str2int(s1@) });
            lemma_valid_bit_string_zero();
        }
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    // Handle multiplication by one
    if s2.len() == 1 && s2[0] == '1' {
        proof {
            lemma_str2int_single_one();
            lemma_multiplication_one(str2int(s1@));
        }
        return s1;
    }
    
    if s1.len() == 1 && s1[0] == '1' {
        proof {
            lemma_str2int_single_one();
            lemma_multiplication_one(str2int(s2@));
        }
        return s2;
    }
    
    // Implement binary multiplication using shift and add
    let mut result = Vec::new();
    result.push('0');
    
    let mut i = 0;
    let mut current_s1 = s1.clone();
    
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            valid_bit_string(result@),
            valid_bit_string(current_s1@),
            valid_bit_string(s1@),
            valid_bit_string(s2@)
    {
        let bit_pos = s2.len() - 1 - i;
        let current_bit = s2[bit_pos];
        
        if current_bit == '1' {
            let partial_product = binary_multiply_by_char(current_s1.clone(), '1');
            let sum_result = add(result@, partial_product@);
            result = seq_to_vec(sum_result);
        }
        
        if i + 1 < s2.len() {
            current_s1 = shift_left(current_s1);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}