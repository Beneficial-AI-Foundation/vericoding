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
fn min_exec(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

/* helper modified by LLM (iteration 3): renamed min to min_exec to avoid name conflict with spec fn */
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
/* code modified by LLM (iteration 3): updated to call min_exec instead of min */
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_a(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        if s[i] == 'a' {
            count += 1;
        }
        i += 1;
    }
    let temp = if count == 0 { 0 } else { 2 * count - 1 };
    let result = min_exec(temp, s.len());
    result
}
// </vc-code>


}

fn main() {}