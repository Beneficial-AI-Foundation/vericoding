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

proof fn lemma_max_occurrence_upper_bound(s: Seq<int>, col: int)
    decreases s.len()
    ensures
        max_occurrence(s) >= count_occurrences(s, col),
{
    if s.len() > 0 {
        let tail = s.subrange(1, s.len() as int);
        lemma_max_occurrence_upper_bound(tail, col);
        reveal(max_occurrence);
        reveal(count_occurrences);
    }
}

proof fn lemma_max_occurrence_exists(s: Seq<int>)
    requires
        s.len() >= 0,
    decreases s.len()
    ensures
        exists|col_val: int| max_occurrence(s) == count_occurrences(s, col_val),
{
    if s.len() == 0 {
        assert(max_occurrence(s) == 0);
        assert(count_occurrences(s, 0) == 0);
        assert(exists|col_val: int| max_occurrence(s) == count_occurrences(s, col_val));
    } else {
        let first_val = s[0];
        let tail = s.subrange(1, s.len() as int);
        lemma_max_occurrence_exists(tail);
        reveal(max_occurrence);
        reveal(count_occurrences);
        if count_occurrences(s, first_val) > max_occurrence(tail) {
            assert max_occurrence(s) == count_occurrences(s, first_val);
            assert exists|col_val: int| max_occurrence(s) == count_occurrences(s, col_val);
        } else {
            assert max_occurrence(s) == max_occurrence(tail);
            assert exists|col_val: int| max_occurrence(tail) == count_occurrences(tail, col_val);
        }
    }
}

spec fn max_occurrence(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let tail = s.subrange(1, s.len() as int);
        let tail_max = max_occurrence(tail);
        let current_count = count_occurrences(s, s[0]);
        if current_count > tail_max { current_count } else { tail_max }
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
    /* code modified by LLM (iteration 5): Fixed compilation errors and added proper loop invariants */
    let seq = squares@.map(|i: int, v: i8| v as int);
    let mut max_count = 0;
    let mut col = 1;
    
    while col <= n as int
        invariant
            1 <= col <= n as int + 1,
            max_count == max_occurrence(seq.subrange(0, col)),
    {
        let mut count = 0;
        let mut i = 0;
        
        while i < m as int
            invariant
                0 <= i <= m as int,
                count == count_occurrences(seq.subrange(0, i), col),
        {
            if seq@[i as int] == col {
                count += 1;
            }
            i += 1;
        }
        
        if count > max_count {
            max_count = count;
        }
        
        col += 1;
    }
    
    proof {
        lemma_max_occurrence_exists(seq);
        assert(max_count == max_occurrence(seq));
        assert(exists|col_val: int| max_count == count_occurrences(seq, col_val));
    }
    
    max_count as i8
}
// </vc-code>


}

fn main() {}