// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches in sequence indexing and bounds by casting loop variables to int in invariants */
    if n > 26 {
        return -1;
    }
    let mut distinct: i32 = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= (i as int) <= (n as int),
            distinct == count_distinct_chars(s@.subrange(0, i as int)),
        decreases (n as int - i as int)
    {
        let mut found = false;
        let mut j = 0;
        while j < i
            invariant
                0 <= (i as int) < (n as int),
                0 <= (j as int) <= (i as int),
                found ==> exists |k: int| 0 <= k < (j as int) && s@[k] == s@[i as int],
                !found ==> forall |k: int| 0 <= k < (j as int) ==> s@[k] != s@[i as int],
            decreases (i as int - j as int)
        {
            if s[j] == s[i] {
                found = true;
            }
            j += 1;
        }
        if !found {
            distinct += 1;
        }
        i += 1;
    }
    (n as i32) - distinct
}
// </vc-code>


}

fn main() {}