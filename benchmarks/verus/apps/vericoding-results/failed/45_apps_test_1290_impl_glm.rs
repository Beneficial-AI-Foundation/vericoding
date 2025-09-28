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
/* helper modified by LLM (iteration 4): fixed clause order (ensures before decreases) */
proof fn count_occurrences_append_lemma(s: Seq<int>, x: int)
    ensures
        forall|c: int| 
            count_occurrences(s.push(x), c) == count_occurrences(s, c) + (if x == c { 1 } else { 0 })
    decreases s.len()
{
    if s.len() == 0 {
        assert(forall|c: int| 
            count_occurrences(s.push(x), c) == (if x == c { 1 } else { 0 }));
        assert(forall|c: int| 
            count_occurrences(s, c) == 0);
        assert(forall|c: int| 
            count_occurrences(s.push(x), c) == count_occurrences(s, c) + (if x == c { 1 } else { 0 }));
    } else {
        let s_last = s.last();
        let s_init = s.drop_last();
        count_occurrences_append_lemma(s_init, x); // recursive call
        assert(forall|c: int| 
            count_occurrences(s.push(x), c) == 
                (if s_last == c { 1 } else { 0 }) + count_occurrences(s_init.push(x), c));
        assert(forall|c: int| 
            count_occurrences(s_init.push(x), c) == 
                count_occurrences(s_init, c) + (if x == c { 1 } else { 0 }));
        assert(forall|c: int| 
            count_occurrences(s, c) == 
                (if s_last == c { 1 } else { 0 }) + count_occurrences(s_init, c));
        assert(forall|c: int| 
            count_occurrences(s.push(x), c) == 
                count_occurrences(s, c) + (if x == c { 1 } else { 0 }));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, squares: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m as int, squares@.map(|i: int, v: i8| v as int))
    ensures correct_result(n as int, squares@.map(|i: int, v: i8| v as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed helper function call */
{
    let mut freq: Vec<i8> = vec![0; n as usize];
    let mut j: i8 = 0;

    while j < m
        invariant
            0 <= j <= m,
            forall|c: int| 1 <= c <= n ==> 
                (freq@[c-1] as int) == count_occurrences(squares@.subrange(0, j as int), c),
        decreases m - j
    {
        let square = squares[j as usize];
        let index = (square - 1) as usize;
        freq[index] = freq[index] + 1;

        proof {
            count_occurrences_append_lemma(squares@.subrange(0, j as int), square as int);
        }

        j += 1;
    }

    let mut min_freq = freq[0];
    let mut i: i8 = 1;

    while i < n
        invariant
            1 <= i <= n,
            forall|k: int| 0 <= k < i ==> min_freq <= freq@[k],
            exists|k: int| 0 <= k < i && min_freq == freq@[k],
        decreases n - i
    {
        if freq[i as usize] < min_freq {
            min_freq = freq[i as usize];
        }
        i += 1;
    }

    min_freq
}
// </vc-code>


}

fn main() {}