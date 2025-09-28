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
/* helper modified by LLM (iteration 5): add a dummy function to satisfy compilation */
fn dummy() {}
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
/* code modified by LLM (iteration 5): use `Set::empty()` to initialize the set, cast `i` to `int` for sequence indexing, and appropriately cast `num_distinct_chars` from `nat` to `int` */
{
    let s_seq = s@;
    let mut i: usize = 0;
    let mut distinct_chars: Set<char> = Set::empty();

    while i < n
        invariant
            0 <= i && i <= n,
            // distinct_chars contains all unique characters encountered so far
            forall|j: int| 0 <= j < i as int ==> #[trigger] distinct_chars.contains(s_seq.index(j as int)),
            distinct_chars <= s_seq.to_set(),
        decreases n - i
    {
        distinct_chars = distinct_chars.insert(s_seq.index(i as int));
        i = i + 1;
    }

    if n > 26 {
        -1
    } else {
        let ghost num_distinct_chars: int = distinct_chars.len() as int;
        (n as i32 - num_distinct_chars as i32)
    }
}
// </vc-code>


}

fn main() {}