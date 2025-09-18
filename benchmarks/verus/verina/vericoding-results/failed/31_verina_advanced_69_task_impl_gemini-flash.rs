// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to helper, as all errors are in main code. */
proof fn lemma_binary_search_properties(xs: &Vec<i32>, target: i32, low: int, high: int, mid: int)
    requires
        0 <= low < high <= xs.len(),
        0 <= mid < xs.len(),
        forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
        forall|i: int| 0 <= i < low ==> xs[i] < target,
        forall|i: int| high <= i < xs.len() ==> xs[i] >= target,
    ensures
        (xs[mid] < target) ==> (forall|i_idx: int| 0 <= i_idx <= mid ==> xs[i_idx] < target),
        (xs[mid] >= target) ==> (forall|i_idx: int| mid <= i_idx < xs.len() ==> xs[i_idx] >= target),
{
    if xs[mid] < target {
        assert forall|i_idx: int| 0 <= i_idx <= mid implies xs[i_idx] < target by {
            if i_idx < low {
                assert(xs[i_idx] < target); // from requires
            } else if i_idx >= low && i_idx <= mid {
                if 0 <= i_idx < xs.len() && 0 <= mid < xs.len() {
                    assert(xs[i_idx] <= xs[mid]); // because xs is sorted non-decreasingly
                    assert(xs[mid] < target);
                }
            }
        }
    } else { // xs[mid] >= target
        assert forall|i_idx: int| mid <= i_idx < xs.len() implies xs[i_idx] >= target by {
            if i_idx >= high {
                 assert(xs[i_idx] >= target); // from requires
            } else if i_idx >= mid && i_idx < high {
                if 0 <= i_idx < xs.len() && 0 <= mid < xs.len() {
                    assert(xs[i_idx] >= xs[mid]); // because xs is sorted non-decreasingly
                    assert(xs[mid] >= target);
                }
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
/* code modified by LLM (iteration 5): Changed `int` types to `usize` for `low` and `high` and removed `xs.len() as int` casts to fix compilation errors. */
{
    let mut low: usize = 0;
    let mut high: usize = xs.len();

    while low < high
        invariant
            0 <= low as int <= high as int <= xs.len() as int,
            forall|i: int| 0 <= i < low as int ==> xs[i] < target,
            forall|i: int| high as int <= i < xs.len() as int ==> xs[i] >= target,
            forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        // Ensure mid is a valid index before accessing xs[mid]
        if mid >= xs.len() {
            low = xs.len(); // This branch implies target is greater than all elements
            break;
        }

        if xs[mid] < target {
            proof {
                if low < high {
                    lemma_binary_search_properties(xs, target, low as int, high as int, mid as int);
                }
            }
            low = mid + 1;
        } else {
            proof {
                if low < high {
                    lemma_binary_search_properties(xs, target, low as int, high as int, mid as int);
                }
            }
            high = mid;
        }
    }
    low
}
// </vc-code>

}
fn main() {}