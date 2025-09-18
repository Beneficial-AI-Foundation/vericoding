// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed precondition bounds to match usage */
proof fn lemma_sorted_implies_prefix(xs: &Vec<i32>, i: int, j: int, target: i32)
    requires
        forall|a: int, b: int| 0 <= a < b < xs.len() ==> xs[a] < xs[b],
        0 <= i <= j < xs.len(),
        xs[j] < target,
    ensures
        forall|k: int| i <= k <= j ==> xs[k] < target,
{
    assert forall|k: int| i <= k <= j implies xs[k] < target by {
        if k < j {
            assert(xs[k] < xs[j]);
            assert(xs[j] < target);
        } else {
            assert(k == j);
            assert(xs[k] == xs[j]);
        }
    }
}

proof fn lemma_sorted_implies_suffix(xs: &Vec<i32>, i: int, j: int, target: i32)
    requires
        forall|a: int, b: int| 0 <= a < b < xs.len() ==> xs[a] < xs[b],
        0 <= i <= j < xs.len(),
        target <= xs[i],
    ensures
        forall|k: int| i <= k <= j ==> target <= xs[k],
{
    assert forall|k: int| i <= k <= j implies target <= xs[k] by {
        if i < k {
            assert(xs[i] < xs[k]);
            assert(target <= xs[i]);
        } else {
            assert(k == i);
            assert(xs[k] == xs[i]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected lemma calls with proper bounds */
    let mut left: usize = 0;
    let mut right: usize = xs.len();
    
    while left < right
        invariant
            left <= right,
            right <= xs.len(),
            forall|i: int| 0 <= i < left ==> xs[i] < target,
            forall|i: int| right <= i < xs.len() ==> target <= xs[i],
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if xs[mid] < target {
            proof {
                lemma_sorted_implies_prefix(xs, 0, mid as int, target);
            }
            left = mid + 1;
        } else {
            if xs.len() > 0 {
                proof {
                    lemma_sorted_implies_suffix(xs, mid as int, (xs.len() - 1) as int, target);
                }
            }
            right = mid;
        }
    }
    
    left
}
// </vc-code>

}
fn main() {}