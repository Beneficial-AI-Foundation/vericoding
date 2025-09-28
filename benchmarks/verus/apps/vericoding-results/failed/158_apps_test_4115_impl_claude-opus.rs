// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1
}

spec fn count_mismatches_up_to(s: Seq<char>, limit: int) -> int
    decreases limit
{
    if limit <= 0 || s.len() < 1 { 
        0 
    } else {
        let n = s.len() as int - 1;
        let mismatch: int = if limit > 0 && limit <= s.len() && s[limit-1] != s[n - (limit-1)] { 1 } else { 0 };
        count_mismatches_up_to(s, limit-1) + mismatch
    }
}

spec fn count_mismatches(s: Seq<char>) -> int {
    if s.len() >= 1 {
        count_mismatches_up_to(s, s.len() as int)
    } else {
        0
    }
}

spec fn valid_result(s: Seq<char>, result: int) -> bool {
    if valid_input(s) {
        result >= 0 && result <= s.len() / 2 && result == (count_mismatches(s) / 2)
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_mismatches_properties(s: Seq<char>, i: int)
    requires
        s.len() >= 1,
        0 <= i <= s.len(),
    ensures
        count_mismatches_up_to(s, i) >= 0,
        count_mismatches_up_to(s, i) <= i,
    decreases i
{
    if i <= 0 {
        assert(count_mismatches_up_to(s, i) == 0);
    } else {
        lemma_count_mismatches_properties(s, i - 1);
        let n = s.len() as int - 1;
        let mismatch: int = if i > 0 && i <= s.len() && s[i-1] != s[n - (i-1)] { 1 } else { 0 };
        assert(count_mismatches_up_to(s, i) == count_mismatches_up_to(s, i - 1) + mismatch);
        assert(mismatch >= 0 && mismatch <= 1);
    }
}

/* helper modified by LLM (iteration 5): Removed while loop from proof function, using recursion instead */
proof fn lemma_count_even_recursive(s: Seq<char>, i: int)
    requires
        s.len() >= 1,
        0 <= i <= s.len(),
    ensures
        count_mismatches_up_to(s, i) % 2 == 0,
    decreases s.len() - i
{
    if i >= s.len() {
        assert(count_mismatches_up_to(s, s.len() as int) % 2 == 0);
    } else if i == 0 {
        assert(count_mismatches_up_to(s, 0) == 0);
    } else {
        let n = s.len() as int - 1;
        let j = n - (i - 1);
        if i - 1 < j {
            lemma_count_even_recursive(s, i - 1);
            let mismatch = if s[i-1] != s[j] { 1 } else { 0 };
            if j == i {
                assert(count_mismatches_up_to(s, i) % 2 == 0);
            }
        }
    }
}

proof fn lemma_count_even(s: Seq<char>)
    requires
        s.len() >= 1,
    ensures
        count_mismatches(s) % 2 == 0,
{
    lemma_count_even_recursive(s, s.len() as int);
    assert(count_mismatches(s) == count_mismatches_up_to(s, s.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures valid_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation focusing on counting mismatches */
    let n = s.len();
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_count_mismatches_properties(s@, n as int);
        lemma_count_even(s@);
    }
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == s.len(),
            count >= 0,
            count as int <= i as int,
    {
        let j = n - 1 - i;
        if s[i] != s[j] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(count as int <= n as int / 2);
        assert(count >= 0);
    }
    
    count
}
// </vc-code>


}

fn main() {}