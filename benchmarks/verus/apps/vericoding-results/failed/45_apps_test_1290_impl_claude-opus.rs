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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, squares: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int))
    ensures correct_result(n as int, squares@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed lambda from trigger by using simpler invariant structure */
    let mut min_count: i8 = m;
    let mut col: i8 = 1;
    
    while col <= n
        invariant
            1 <= col <= n + 1,
            0 <= min_count <= m,
            m == squares.len(),
            valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int)),
            forall|c: int| 1 <= c < col ==> min_count as int <= #[trigger] count_occurrences(squares@.map(|i: int, v: i8| v as int), c),
            col > 1 ==> exists|c: int| 1 <= c < col && min_count as int == count_occurrences(squares@.map(|i: int, v: i8| v as int), c),
        decreases n - col
    {
        let mut count: i8 = 0;
        let mut i: usize = 0;
        
        while i < squares.len()
            invariant
                0 <= i <= squares.len(),
                0 <= count <= i,
                m == squares.len(),
                count as int == count_occurrences(squares@.map(|i: int, v: i8| v as int).subrange(0, i as int), col as int),
            decreases squares.len() - i
        {
            if squares[i] == col {
                count = count + 1;
            }
            i = i + 1;
        }
        
        assert(squares@.map(|i: int, v: i8| v as int).subrange(0, squares.len() as int) =~= squares@.map(|i: int, v: i8| v as int));
        assert(count as int == count_occurrences(squares@.map(|i: int, v: i8| v as int), col as int));
        
        if count < min_count {
            min_count = count;
        }
        
        col = col + 1;
    }
    
    min_count
}
// </vc-code>


}

fn main() {}