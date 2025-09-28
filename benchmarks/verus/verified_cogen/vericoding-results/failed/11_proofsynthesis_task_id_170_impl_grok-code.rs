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
spec fn loop_sum(arr: Seq<i64>, start: int, k: int) -> int
    requires start <= k && k <= arr.len(),
    decreases k - start,
{
    if k <= start {
        0
    } else {
        loop_sum(arr, start, k - 1) + (arr[k - 1] as int)
    }
}

/* helper modified by LLM (iteration 4): fixed decreases clause and seq index */

proof fn lemma_loop_sum(arr: Seq<i64>, start: int, k: int)
    requires start <= k && k <= arr.len(),
    ensures loop_sum(arr, start, k) == sum_to(arr.subrange(start, k)),
    decreases k - start,
{
    if k > start {
        lemma_loop_sum(arr, start, k - 1);
        let sub = arr.subrange(start, k);
        assert(sub.drop_last() == arr.subrange(start, k - 1));
        assert(sub.last() as int == arr[k - 1] as int);
    }
}

/* helper modified by LLM (iteration 4): renamed function and fixed ensures */
// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)

    requires
        0 <= start <= end,
        start <= end < arr.len(),

    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arr@[i] to arr[i] for vector indexing */
    let mut sum = 0i128;
    let mut i = start;
    while i <= end
        invariant
            0 <= start <= i <= end + 1 <= (arr.len() as int),
            end < arr.len(),
            (sum as int) == loop_sum(arr@, start as int, i as int),
    {
        sum = sum + (arr[i] as i128);
        i += 1;
    }
    proof {
        lemma_loop_sum(arr@, start as int, (end + 1) as int);
    }
    sum
}
// </vc-code>

}
fn main() {}