// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_a(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[0] == 'a' { 1 as int } else { 0 as int }) + count_a(s.subrange(1, s.len() as int))
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && exists|i: int| 0 <= i < s.len() && s[i] == 'a'
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() > 0 && count_a(s) > s.len() as int / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed prefix lemma to handle bounds correctly */
proof fn lemma_count_a_bounds(s: Seq<char>)
    ensures
        0 <= count_a(s) <= s.len() as int,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_a_bounds(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_count_a_prefix(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_a(s.subrange(0, i)) <= count_a(s),
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(count_a(s.subrange(0, 0)) == 0);
        lemma_count_a_bounds(s);
    } else if s.len() == 0 {
        assert(i == 0);
    } else {
        assert(i >= 1);
        assert(s.subrange(0, i).len() > 0);
        let sub_prefix = s.subrange(0, i - 1);
        lemma_count_a_prefix(s, i - 1);
        if s[i - 1] == 'a' {
            assert(count_a(s.subrange(0, i)) == count_a(sub_prefix) + 1);
        } else {
            assert(count_a(s.subrange(0, i)) == count_a(sub_prefix));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@),
    ensures 
        result >= 1,
        result <= s.len(),
        result == min(2 * count_a(s@) - 1, s.len() as int) as usize,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using ghost variables for int calculations */
    let mut count_as: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count_as as int == count_a(s@.subrange(0, i as int)),
            count_as <= i,
        decreases s.len() - i
    {
        if s[i] == 'a' {
            count_as = count_as + 1;
        }
        i = i + 1;
        
        proof {
            lemma_count_a_prefix(s@, i as int);
        }
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
        lemma_count_a_bounds(s@);
        assert(count_as as int == count_a(s@));
        assert(count_as >= 1) by {
            assert(valid_input(s@));
        }
    }
    
    if count_as >= 1 && 2 * count_as >= 1 {
        proof {
            let ghost count_as_int = count_as as int;
            let ghost formula_result_int = 2 * count_as_int - 1;
            
            if formula_result_int <= s.len() as int {
                assert(min(2 * count_a(s@) - 1, s.len() as int) == 2 * count_a(s@) - 1);
            } else {
                assert(min(2 * count_a(s@) - 1, s.len() as int) == s.len() as int);
            }
        }
        
        let formula_result = 2 * count_as - 1;
        let result = if formula_result <= s.len() {
            formula_result
        } else {
            s.len()
        };
        
        result
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}