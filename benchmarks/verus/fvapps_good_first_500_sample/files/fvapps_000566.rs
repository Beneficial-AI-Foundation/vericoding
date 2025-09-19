// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_balanced_bracket_char(c: char) -> bool {
    c == '(' || c == ')'
}

spec fn count_opening_brackets(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else if s[start] == '(' {
        1 + count_opening_brackets(s, start + 1, end)
    } else {
        count_opening_brackets(s, start + 1, end)
    }
}

spec fn count_closing_brackets(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else if s[start] == ')' {
        1 + count_closing_brackets(s, start + 1, end)
    } else {
        count_closing_brackets(s, start + 1, end)
    }
}

fn solve_bracket_sequence(s: &Vec<char>, queries: &Vec<usize>) -> (result: Vec<i32>)
    requires 
        s.len() > 0,
        queries.len() > 0,
        forall|c: char| s@.contains(c) ==> (c == '(' || c == ')'),
        forall|q: usize| #[trigger] queries@.contains(q) ==> (0 < q && q <= s.len()),
    ensures 
        result.len() == queries.len(),
        forall|i: int| 0 <= i < result.len() ==> (-1 <= result[i] && result[i] <= s.len() as i32),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}