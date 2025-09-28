// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n
}

spec fn max_in_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    via max_in_seq_decreases
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail = s.subrange(1, s.len() as int);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max { s[0] } else { tail_max }
    }
}

#[via_fn]
proof fn max_in_seq_decreases(s: Seq<int>) {
    assume(false);
}

spec fn valid_result(n: int, heights: Seq<int>, result: int) -> bool
    recommends valid_input(n, heights)
{
    result == max_in_seq(heights) &&
    forall|i: int| 0 <= i < heights.len() ==> heights[i] <= result &&
    exists|i: int| 0 <= i < heights.len() && heights[i] == result
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [Reviewed lemma proofs and confirmed logic.] */
proof fn lemma_max_in_seq_is_le(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[i] <= max_in_seq(s),
    decreases s.len()
{
    let m = max_in_seq(s);
    if s.len() > 1 {
        let tail = s.subrange(1, s.len() as int);
        lemma_max_in_seq_is_le(tail);
        let m_tail = max_in_seq(tail);
        
        assert(m >= s[0]);
        assert(m >= m_tail);
        
        assert forall|i: int| 1 <= i < s.len() implies s[i] <= m by {
            let j = i - 1;
            assert(tail[j] == s[i]);
            assert(tail[j] <= m_tail);
            assert(s[i] <= m);
        }
    }
}

proof fn lemma_max_in_seq_is_in(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == max_in_seq(s),
    decreases s.len()
{
    let m = max_in_seq(s);
    if s.len() > 1 {
        let tail = s.subrange(1, s.len() as int);
        let m_tail = max_in_seq(tail);
        if s[0] >= m_tail {
            assert(m == s[0]);
        } else {
            lemma_max_in_seq_is_in(tail);
            assert(m == m_tail);
            let j = choose |j: int| 0 <= j < tail.len() && tail[j] == m_tail;
            let i = j + 1;
            assert(s[i] == tail[j]);
            assert(s[i] == m);
            assert(0 <= i < s.len());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, heights@.map(|i, x: i8| x as int))
    ensures valid_result(n as int, heights@.map(|i, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [Fixed `ghost let` syntax to `let ghost`.] */
    let ghost n_int = n as int;
    let ghost heights_int = heights@.map(|_i, x: i8| x as int);

    let mut max = heights[(n - 1) as usize];
    let mut i: i8 = n - 2;

    while i >= 0
        invariant
            heights@.len() == n_int,
            n_int > 0,
            -1 <= i < n_int - 1,
            max as int == max_in_seq(heights_int.subrange((i + 1) as int, n_int)),
        decreases i
    {
        let current_h = heights[i as usize];
        if current_h > max {
            max = current_h;
        }
        i = i - 1;
    }

    proof {
        assert(max as int == max_in_seq(heights_int));
        lemma_max_in_seq_is_le(heights_int);
        lemma_max_in_seq_is_in(heights_int);
    }
    
    max
}
// </vc-code>


}

fn main() {}