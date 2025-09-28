// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec for prefix sum of sequence */
spec fn seq_prefix_sum(s: Seq<i64>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        seq_prefix_sum(s, n - 1) + s@[n - 1]
    }
}

/* helper modified by LLM (iteration 5): proof that prefix sum of full sequence equals sum_to */
proof fn seq_prefix_sum_matches_sum_to(s: Seq<i64>)
    ensures
        seq_prefix_sum(s, s.len()) == sum_to(s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        seq_prefix_sum_matches_sum_to(s.drop_last());
        proof {
            assert(seq_prefix_sum(s, s.len()) == seq_prefix_sum(s, s.len() - 1) + s@[s.len() - 1]);
            assert(sum_to(s) == sum_to(s.drop_last()) + s.last());
            assert(seq_prefix_sum(s, s.len() - 1) == sum_to(s.drop_last()));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): accumulate using nat index and maintain invariant relating to seq_prefix_sum */
    let mut acc: i128 = 0;
    let mut i: nat = 0;
    while i < arr@.len()
        invariant
            seq_prefix_sum(arr@, i) == (acc as int),
        decreases arr@.len() - i
    {
        let old = acc;
        acc = old + (arr[i as usize] as i128);
        i = i + 1;
        proof {
            assert(seq_prefix_sum(arr@, i) == seq_prefix_sum(arr@, i - 1) + arr@[i - 1]);
            assert((old as int) + arr@[i - 1] == (acc as int));
            assert(seq_prefix_sum(arr@, i) == (acc as int));
        }
    }
    proof {
        assert(seq_prefix_sum(arr@, arr@.len()) == (acc as int));
        seq_prefix_sum_matches_sum_to(arr@);
        assert(sum_to(arr@) == (acc as int));
    }
    acc
}
// </vc-code>

}
fn main() {}