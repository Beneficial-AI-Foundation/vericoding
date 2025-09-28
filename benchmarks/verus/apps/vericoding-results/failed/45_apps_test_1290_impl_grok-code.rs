// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, squares: Seq<int>) -> bool {
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    squares.len() == m &&
    forall|i: int| 0 <= i < squares.len() ==> #[trigger] squares[i] >= 1 && #[trigger] squares[i] <= n
}

spec fn count_occurrences(s: Seq<int>, value: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == value { 1int } else { 0int }) + count_occurrences(s.subrange(1, s.len() as int), value)
    }
}

spec fn correct_result(n: int, squares: Seq<int>, result: int) -> bool {
    0 <= result <= squares.len() &&
    (forall|col: int| 1 <= col <= n ==> result <= #[trigger] count_occurrences(squares, col)) &&
    (exists|col: int| 1 <= col <= n && result == #[trigger] count_occurrences(squares, col))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, squares: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int))
    ensures correct_result(n as int, squares@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added #[trigger] to quantifier in invariant for correct triggering */
{
    let mut current_min = count_occurrences_exec(&squares, 1i8);
    let mut col = 2i8;
    while col <= n
        invariant
            1 <= col as int <= (n as int) + 1,
            forall|cc: int| 1 <= cc < col as int ==> #[trigger] count_occurrences(squares@.map(|i: int, v: i8| v as int), cc) >= current_min as int,
            exists|cc: int| 1 <= cc < col as int && count_occurrences(squares@.map(|i: int, v: i8| v as int), cc) == current_min as int,
        decreases (n as int) - (col as int),
    {
        let curr_count = count_occurrences_exec(&squares, col);
        if curr_count < current_min {
            current_min = curr_count;
        }
        col = col + 1;
    }
    (current_min as i8)
}
// </vc-code>


}

fn main() {}