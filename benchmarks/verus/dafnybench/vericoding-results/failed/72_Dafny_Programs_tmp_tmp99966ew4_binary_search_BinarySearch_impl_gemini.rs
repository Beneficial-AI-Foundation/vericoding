// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, helpers are correct. */
proof fn lemma_search_lt(a: &[int], value: int, mid: int)
    requires
        sorted(a),
        0 <= mid < a.len(),
        a@[mid] < value,
    ensures
        forall|k: int| 0 <= k <= mid ==> a@[k] != value,
{
}

/* helper modified by LLM (iteration 5): No changes needed, helpers are correct. */
proof fn lemma_search_gt(a: &[int], value: int, mid: int)
    requires
        sorted(a),
        0 <= mid < a.len(),
        a@[mid] > value,
    ensures
        forall|k: int| mid <= k < a.len() ==> a@[k] != value,
{
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed a compilation error by moving the assertion into a proof block and using spec-indexing. */
    let mut low: usize = 0;
    let mut high: usize = a.len();

    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|k: int| 0 <= k < a.len() && a@[k] == value ==> (low as int) <= k < (high as int),
        decreases high - low
    {
        let mid = low + (high - low) / 2;

        if a[mid] < value {
            proof {
                lemma_search_lt(a, value, mid as int);
            }
            low = mid + 1;
        } else if a[mid] > value {
            proof {
                lemma_search_gt(a, value, mid as int);
            }
            high = mid;
        } else {
            proof {
                assert(a@[mid as int] == value);
            }
            return mid as i32;
        }
    }

    -1
}
// </vc-code>

}
fn main() {}