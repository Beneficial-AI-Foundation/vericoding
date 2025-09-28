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
/* helper modified by LLM (iteration 5): no changes needed, it is correct */
proof fn lemma_count_occurrences_upper_bound(s: Seq<int>, value: int)
    ensures count_occurrences(s, value) <= s.len()
    decreases s.len()
pure
{
    if s.len() > 0 {
        lemma_count_occurrences_upper_bound(s.subrange(1, s.len() as int), value);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, squares: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int))
    ensures correct_result(n as int, squares@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): moved squares_spec definition into proof block to fix compilation errors */
{
    let mut min_count: i8 = (m + 1) as i8;

    let mut col: i8 = 1;
    while col <= n
        invariant
            1 <= col as int <= n as int + 1,
            min_count as int >= 0,
            min_count as int <= m as int + 1,
            ({
                let squares_spec = squares@.map(|idx: nat, v: i8| v as int);
                (forall|i_int: int| 1 <= i_int < col as int ==> min_count as int <= count_occurrences(squares_spec, i_int))
            }),
            ({
                let squares_spec = squares@.map(|idx: nat, v: i8| v as int);
                (exists|i_int: int| 1 <= i_int < col as int && min_count as int == count_occurrences(squares_spec, i_int)) || min_count as int == m as int + 1
            })
        decreases (n - col) as int
    {
        proof {
            let squares_spec = squares@.map(|idx: nat, v: i8| v as int);
            lemma_count_occurrences_upper_bound(squares_spec, col as int);
            let current_count_spec_val: int = count_occurrences(squares_spec, col as int);
            if current_count_spec_val < min_count as int {
                min_count = current_count_spec_val as i8;
            }
        }
        col = col + 1;
    }

    if n == 0 {
        0
    } else {
        min_count
    }
}
// </vc-code>


}

fn main() {}