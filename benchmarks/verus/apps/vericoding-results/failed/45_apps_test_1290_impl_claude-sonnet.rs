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
/* helper modified by LLM (iteration 5): changed spec functions to exec functions and fixed type annotations */
fn count_column_occurrences(squares: Seq<int>, col: int) -> (result: int)
    decreases squares.len()
{
    if squares.len() == 0 {
        0int
    } else {
        let first_count: int = if squares[0] == col { 1int } else { 0int };
        first_count + count_column_occurrences(squares.subrange(1, squares.len()), col)
    }
}

fn find_min_count(n: int, squares: Seq<int>) -> (result: int)
    requires
        n >= 1,
        squares.len() >= 0,
        forall|i: int| 0 <= i < squares.len() ==> squares[i] >= 1 && squares[i] <= n
    decreases n
{
    if n == 1 {
        count_column_occurrences(squares, 1)
    } else {
        let current_count = count_column_occurrences(squares, n);
        let rest_min = find_min_count(n - 1, squares);
        if current_count < rest_min { current_count } else { rest_min }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, squares: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int))
    ensures correct_result(n as int, squares@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented iterative solution without spec functions */
    let mut min_count = squares.len();
    let mut col = 1i8;
    
    while col <= n
        invariant
            1 <= col <= n + 1,
            min_count <= squares.len(),
            (forall|c: int| 1 <= c < col ==> min_count <= count_occurrences(squares@.map(|i: int, v: i8| v as int), c)),
            (col > 1 ==> exists|c: int| 1 <= c < col && min_count == count_occurrences(squares@.map(|i: int, v: i8| v as int), c))
        decreases n - col
    {
        let mut count = 0usize;
        let mut i = 0usize;
        
        while i < squares.len()
            invariant
                0 <= i <= squares.len(),
                count <= i
            decreases squares.len() - i
        {
            if squares[i] == col {
                count = count + 1;
            }
            i = i + 1;
        }
        
        if count < min_count {
            min_count = count;
        }
        col = col + 1;
    }
    
    min_count as i8
}
// </vc-code>


}

fn main() {}