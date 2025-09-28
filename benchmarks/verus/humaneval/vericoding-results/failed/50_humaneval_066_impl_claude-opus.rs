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
/* helper modified by LLM (iteration 5): Fixed lemma to handle recursive definition and edge cases properly */
proof fn lemma_sum_uppercase_nonnegative(s: Seq<char>)
    ensures sum_of_uppercase_ascii(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_of_uppercase_ascii(s) == 0);
    } else {
        lemma_sum_uppercase_nonnegative(s.subrange(1, s.len() as int));
        let c = s[0];
        if 'A' <= c && c <= 'Z' {
            assert(c as int >= 65);
            assert(sum_of_uppercase_ascii(s.subrange(1, s.len() as int)) >= 0);
        }
    }
}

proof fn lemma_sum_extend(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum_of_uppercase_ascii(s.subrange(0, i + 1)) == {
            let prefix_sum = if i == 0 { 0 } else { sum_of_uppercase_ascii(s.subrange(1, i as int)) };
            let first_contrib = if i > 0 && 'A' <= s[0] && s[0] <= 'Z' { s[0] as int } else { 0 };
            let last_contrib = if 'A' <= s[i] && s[i] <= 'Z' { s[i] as int } else { 0 };
            if i == 0 {
                last_contrib
            } else {
                first_contrib + prefix_sum + last_contrib
            }
        }
{
    if i == 0 {
        assert(s.subrange(0, 1).len() == 1);
        assert(s.subrange(0, 1)[0] == s[0]);
        assert(sum_of_uppercase_ascii(s.subrange(0, 1)) == if 'A' <= s[0] && s[0] <= 'Z' { s[0] as int } else { 0 });
    } else {
        let extended = s.subrange(0, i + 1);
        assert(extended.len() == i + 1);
        assert(extended[0] == s[0]);
        assert(extended.subrange(1, extended.len() as int) =~= s.subrange(1, i + 1));
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
    /* code modified by LLM (iteration 5): Simplified approach using direct iteration with correct invariant */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_sum_uppercase_nonnegative(s@);
        assert(sum_of_uppercase_ascii(s@.subrange(0, 0)) == 0);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            sum >= 0,
            sum <= i32::MAX,
            sum == sum_of_uppercase_ascii(s@.subrange(0, i as int)),
            sum_of_uppercase_ascii(s@.subrange(0, i as int)) <= i32::MAX,
        decreases s.len() - i
    {
        let c = s[i];
        
        proof {
            assert(s@.subrange(0, (i + 1) as int).len() == i + 1);
            if i == 0 {
                assert(s@.subrange(0, 1)[0] == s@[0]);
                assert(sum_of_uppercase_ascii(s@.subrange(0, 1)) == 
                    if 'A' <= s@[0] && s@[0] <= 'Z' { s@[0] as int } else { 0 });
            } else {
                let extended = s@.subrange(0, (i + 1) as int);
                assert(extended[0] == s@[0]);
                assert(extended.subrange(1, extended.len() as int) =~= s@.subrange(1, (i + 1) as int));
            }
            lemma_sum_uppercase_nonnegative(s@.subrange(0, (i + 1) as int));
        }
        
        if 'A' <= c && c <= 'Z' {
            assert(c as i32 >= 65 && c as i32 <= 90);
            assert(sum + (c as i32) <= i32::MAX);
            sum = sum + (c as i32);
        }
        
        i = i + 1;
        
        proof {
            assert(sum == sum_of_uppercase_ascii(s@.subrange(0, i as int)));
        }
    }
    
    assert(s@.subrange(0, s.len() as int) =~= s@);
    sum
}
// </vc-code>


}

fn main() {}