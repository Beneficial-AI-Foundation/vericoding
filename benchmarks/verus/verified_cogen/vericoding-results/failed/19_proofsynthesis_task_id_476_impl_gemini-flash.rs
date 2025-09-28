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
/* helper modified by LLM (iteration 4): Removed `requires` and `decreases` from spec fns `recursive_max_seq` and `recursive_min_seq` as spec functions cannot have them, which caused a compilation error. */
spec fn recursive_max_seq(s: Seq<i32>, idx: int) -> int {
    if idx == 0 {
        s[0] as int
    } else {
        max(recursive_max_seq(s, idx - 1), s[idx] as int)
    }
}
spec fn recursive_min_seq(s: Seq<i32>, idx: int) -> int {
    if idx == 0 {
        s[0] as int
    } else {
        min(recursive_min_seq(s, idx - 1), s[idx] as int)
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
/* code modified by LLM (iteration 4): No code changes made. */
{
    let mut min_val: i32 = arr[0];
    let mut max_val: i32 = arr[0];
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            0 < i,
            i <= arr.len(),
            min_val == recursive_min_seq(arr@, (i - 1) as int),
            max_val == recursive_max_seq(arr@, (i - 1) as int),
        decreases arr.len() - i,
    {
        let current_val = arr[i];
        if current_val < min_val {
            min_val = current_val;
        }
        if current_val > max_val {
            max_val = current_val;
        }
        i = i + 1;
    }

    proof {
        assert(max_val == recursive_max_seq(arr@, (arr.len() - 1) as int));
        assert(min_val == recursive_min_seq(arr@, (arr.len() - 1) as int));
        
        assert(recursive_max_seq(arr@, (arr.len() - 1) as int) == max_rcur(arr@)) by (recursion);
        assert(recursive_min_seq(arr@, (arr.len() - 1) as int) == min_rcur(arr@)) by (recursion);

    }
    (min_val + max_val)
}
// </vc-code>

}
fn main() {}