// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define max over prefix by dropping last until desired length */
spec fn max_prefix(seq: Seq<i32>, n: int) -> (result:int)
    requires
        1 <= n,
        n <= seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == n {
        max_rcur(seq)
    } else {
        max_prefix(seq.drop_last(), n)
    }
}

/* helper modified by LLM (iteration 5): define min over prefix by dropping last until desired length */
spec fn min_prefix(seq: Seq<i32>, n: int) -> (result:int)
    requires
        1 <= n,
        n <= seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == n {
        min_rcur(seq)
    } else {
        min_prefix(seq.drop_last(), n)
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative scan for min and max using helper prefix specs */
    let mut j: usize = 1;
    let mut cur_max: i32 = arr[0];
    let mut cur_min: i32 = arr[0];
    while j < arr.len()
        invariant
            1 <= j,
            j <= arr.len(),
            cur_max as int == max_prefix(arr@, j as int),
            cur_min as int == min_prefix(arr@, j as int),
        decreases
            arr.len() - j
    {
        let v: i32 = arr[j];
        if v > cur_max {
            cur_max = v;
        }
        if v < cur_min {
            cur_min = v;
        }
        j = j + 1;
    }
    cur_max + cur_min
}
// </vc-code>

}
fn main() {}