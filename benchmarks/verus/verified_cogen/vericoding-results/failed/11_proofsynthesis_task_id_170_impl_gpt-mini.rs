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
/* helper modified by LLM (iteration 5): lemma showing sum_to on subrange extended by last element */
proof fn sum_to_subrange_snoc(arr: Seq<i64>, lo: int, hi: int)
    requires
        lo <= hi,
        hi < arr.len(),
    decreases
        hi - lo,
    ensures
        sum_to(arr.subrange(lo, hi + 1)) == sum_to(arr.subrange(lo, hi)) + (arr@[hi] as int),
{
    proof {
        if hi == lo {
            let s = arr.subrange(lo, hi + 1);
            assert s.len() == 1;
            assert sum_to(s) == (s.last() as int);
            assert sum_to(arr.subrange(lo, hi)) == 0;
            assert sum_to(s) == sum_to(arr.subrange(lo, hi)) + (arr@[hi] as int);
        } else {
            let s = arr.subrange(lo, hi + 1);
            assert s.drop_last() == arr.subrange(lo, hi);
            assert s.last() == arr@[hi];
            assert sum_to(s) == sum_to(s.drop_last()) + (s.last() as int);
            assert sum_to(s) == sum_to(arr.subrange(lo, hi)) + (arr@[hi] as int);
        }
    }
}

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
    /* code modified by LLM (iteration 5): iterative summation proving sum equals sum_to of subrange */
    let mut i: int = start as int;
    let end_i: int = end as int;
    let mut acc: int = 0;
    while i <= end_i
        invariant
            start as int <= i,
            i <= end_i + 1,
            acc == sum_to(arr@.subrange(start as int, i)),
        decreases
            end_i + 1 - i
    {
        let cur: int = i;
        acc = acc + (arr@[cur] as int);
        i = i + 1;
        proof {
            sum_to_subrange_snoc(arr@, start as int, cur);
            assert acc == sum_to(arr@.subrange(start as int, i));
        }
    }
    acc as i128
}

// </vc-code>

}
fn main() {}