// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant definitions of min_seq and max_seq to fix compilation error. */
proof fn lemma_max_seq_extend(s: Seq<int>, i: int)
    requires
        0 < i < s.len(),
    ensures
        max_seq(s.subrange(0, i + 1)) == if s[i] >= max_seq(s.subrange(0, i)) { s[i] } else { max_seq(s.subrange(0, i)) },
{
}

proof fn lemma_min_seq_extend(s: Seq<int>, i: int)
    requires
        0 < i < s.len(),
    ensures
        min_seq(s.subrange(0, i + 1)) == if s[i] <= min_seq(s.subrange(0, i)) { s[i] } else { min_seq(s.subrange(0, i)) },
{
}

// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes; the logic is correct but depended on helpers that had a compilation error. */
    let ghost s = a@.map(|_idx: int, x: i32| x as int);
    let mut min = a[0];
    let mut max = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            max as int == max_seq(s.subrange(0, i as int)),
            min as int == min_seq(s.subrange(0, i as int)),
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
        }
        if a[i] < min {
            min = a[i];
        }

        proof {
            lemma_max_seq_extend(s, i as int);
            lemma_min_seq_extend(s, i as int);
        }

        i = i + 1;
    }

    min + max
}
// </vc-code>

}
fn main() {}