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
/* helper modified by LLM (iteration 10): Fixed type issues - use usize for executable code indexing */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires valid_bit_string(s),
    ensures str2int(s.push('0')) == 2 * str2int(s),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push('0') =~= seq!['0']);
    } else {
        assert(s.push('0').subrange(0, s.push('0').len() - 1) =~= s);
    }
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires valid_bit_string(s),
    ensures str2int(s.push('1')) == 2 * str2int(s) + 1,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push('1') =~= seq!['1']);
    } else {
        assert(s.push('1').subrange(0, s.push('1').len() - 1) =~= s);
    }
}

proof fn lemma_div_mod_invariant(dividend: Seq<char>, divisor: Seq<char>, quotient: Seq<char>, remainder: Seq<char>, i: int)
    requires
        valid_bit_string(dividend),
        valid_bit_string(divisor),
        valid_bit_string(quotient),
        valid_bit_string(remainder),
        str2int(divisor) > 0,
        0 <= i <= dividend.len(),
        str2int(remainder) < str2int(divisor),
        str2int(dividend.subrange(0, i)) == str2int(quotient) * str2int(divisor) + str2int(remainder),
    ensures
        i < dividend.len() ==> {
            let new_rem = if dividend[i] == '1' { remainder.push('1') } else { remainder.push('0') };
            valid_bit_string(new_rem) && str2int(new_rem) == 2 * str2int(remainder) + if dividend[i] == '1' { 1nat } else { 0nat }
        },
{
    if i < dividend.len() {
        if dividend[i] == '1' {
            lemma_str2int_append_one(remainder);
        } else {
            lemma_str2int_append_zero(remainder);
        }
    }
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
{
    /* code modified by LLM (iteration 10): Fixed indexing - use usize for j and access new_remainder properly */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    let mut i: usize = 0;

    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            valid_bit_string(quotient@),
            valid_bit_string(remainder@),
            str2int(remainder@) < str2int(divisor@),
            str2int(dividend@.subrange(0, i as int)) == str2int(quotient@) * str2int(divisor@) + str2int(remainder@),
    {
        proof {
            lemma_div_mod_invariant(dividend@, divisor@, quotient@, remainder@, i as int);
        }
        
        let bit = dividend[i];
        remainder.push(bit);
        
        let cmp = compare(remainder@, divisor@);
        if cmp >= 0 {
            quotient.push('1');
            let new_remainder = sub(remainder@, divisor@);
            remainder = Vec::<char>::new();
            let mut j: usize = 0;
            let new_rem_len: usize = new_remainder.len() as usize;
            while j < new_rem_len
                invariant
                    0 <= j <= new_rem_len,
                    j <= new_remainder.len() as usize,
                    remainder@.len() == j as int,
                    forall|k: int| 0 <= k < j as int ==> remainder@[k] == new_remainder[k as int],
                    valid_bit_string(remainder@),
            {
                remainder.push(new_remainder[j as int]);
                j = j + 1;
            }
        } else {
            quotient.push('0');
        }
        
        i = i + 1;
    }
    
    (quotient, remainder)
}
// </vc-code>


}

fn main() {}