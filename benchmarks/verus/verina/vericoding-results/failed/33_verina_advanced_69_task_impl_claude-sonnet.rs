// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed precondition by removing mid < right requirement */
proof fn binary_search_invariant_lemma(xs: &Vec<i32>, left: usize, right: usize, mid: usize, target: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
        left <= right,
        right <= xs.len(),
        left <= mid < right,
        forall|i: int| 0 <= i < left ==> xs[i] < target,
        forall|i: int| right <= i < xs.len() ==> target <= xs[i as int],
    ensures
        xs[mid as int] < target ==> forall|i: int| 0 <= i <= mid ==> xs[i] < target,
        xs[mid as int] >= target ==> forall|i: int| mid <= i < xs.len() ==> target <= xs[i as int],
{
    if xs[mid as int] < target {
        assert forall|i: int| 0 <= i <= mid implies xs[i] < target by {
            if i < left {
                assert(xs[i] < target);
            } else if i == mid {
                assert(xs[i] < target);
            } else {
                assert(left <= i < mid);
                assert(xs[i] < xs[mid as int]);
                assert(xs[mid as int] < target);
                assert(xs[i] < target);
            }
        }
    }
    if xs[mid as int] >= target {
        assert forall|i: int| mid <= i < xs.len() implies target <= xs[i as int] by {
            if i >= right {
                assert(target <= xs[i]);
            } else if i == mid {
                assert(target <= xs[i]);
            } else {
                assert(mid < i < right);
                assert(xs[mid as int] < xs[i]);
                assert(target <= xs[mid as int]);
                assert(target <= xs[i]);
            }
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
    /* code modified by LLM (iteration 5): added explicit bounds check before calling lemma */
    let mut left: usize = 0;
    let mut right: usize = xs.len();
    
    while left < right
        invariant
            left <= right,
            right <= xs.len(),
            forall|i: int| 0 <= i < left ==> xs[i] < target,
            forall|i: int| right <= i < xs.len() ==> target <= xs[i as int],
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        proof {
            assert(left < right);
            assert(mid >= left);
            assert(mid < right);
            binary_search_invariant_lemma(xs, left, right, mid, target);
        }
        
        if xs[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    left
}
// </vc-code>

}
fn main() {}