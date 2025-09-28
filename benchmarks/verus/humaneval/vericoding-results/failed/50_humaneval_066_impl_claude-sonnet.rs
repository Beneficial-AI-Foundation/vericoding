// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_of_uppercase_ascii(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else {
        let c = s[0];
        let rest = sum_of_uppercase_ascii(s.subrange(1, s.len() as int));
        if 'A' <= c && c <= 'Z' { 
            (c as int) + rest
        } else {
            rest
        }
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed assert statement with parentheses */
spec fn sum_uppercase_nonneg(s: Seq<char>) -> bool {
    sum_of_uppercase_ascii(s) >= 0
}

fn lemma_sum_uppercase_nonneg(s: Seq<char>)
    ensures sum_of_uppercase_ascii(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_sum_uppercase_nonneg(s.subrange(1, s.len() as int));
    }
}

fn lemma_sum_uppercase_subrange(s: Seq<char>, i: int)
    requires 0 <= i <= s.len()
    ensures sum_of_uppercase_ascii(s.subrange(0, i)) + sum_of_uppercase_ascii(s.subrange(i, s.len() as int)) == sum_of_uppercase_ascii(s)
    decreases i
{
    if i == 0 {
    } else {
        lemma_sum_uppercase_subrange(s, i - 1);
        assert(s.subrange(0, i) == s.subrange(0, i - 1).push(s[i - 1]));
    }
}
// </vc-helpers>

// <vc-spec>
fn digit_sum(s: Vec<char>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_uppercase_ascii(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assert statement with parentheses */
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_sum_uppercase_nonneg(s@);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result >= 0,
            result == sum_of_uppercase_ascii(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let c = s[i];
        if 'A' <= c && c <= 'Z' {
            result = result + (c as i32);
        }
        
        proof {
            assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == s.len());
        assert(s@.subrange(0, i as int) == s@);
    }
    
    result
}
// </vc-code>


}

fn main() {}