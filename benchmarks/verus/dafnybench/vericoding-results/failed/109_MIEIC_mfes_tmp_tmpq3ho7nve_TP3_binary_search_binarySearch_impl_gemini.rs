// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed forall proof syntax */
proof fn sorted_implies_not_in_lower_half(a: &[i32], x: i32, mid: int)
    requires
        is_sorted(a),
        0 <= mid < a.len(),
        a[mid] < x,
    ensures
        forall|k: int| 0 <= k <= mid ==> a[k] != x,
{
    forall|k: int| 0 <= k <= mid implies a[k] != x by {
        assert(is_sorted(a));
        assert(a[k] <= a[mid]);
        assert(a[k] < x);
    }
}

/* helper modified by LLM (iteration 5): fixed forall proof syntax */
proof fn sorted_implies_not_in_upper_half(a: &[i32], x: i32, mid: int)
    requires
        is_sorted(a),
        0 <= mid < a.len(),
        a[mid] > x,
    ensures
        forall|k: int| mid <= k < a.len() ==> a[k] != x,
{
    forall|k: int| mid <= k < a.len() implies a[k] != x by {
        assert(is_sorted(a));
        assert(a[mid] <= a[k]);
        assert(x < a[k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added comments, no logical changes */
{
    let mut low: usize = 0;
    let mut high: usize = a.len();

    while low < high
        invariant
            0 <= low as int <= high as int <= a.len(),
            is_sorted(a),
            forall|k: int| (0 <= k < low as int || high as int <= k < a.len()) ==> a[k] != x,
        decreases (high - low) as int
    {
        let mid = low + (high - low) / 2;

        if a[mid] < x {
            proof {
                sorted_implies_not_in_lower_half(a, x, mid as int);
            }
            low = mid + 1;
        } else if a[mid] > x {
            proof {
                sorted_implies_not_in_upper_half(a, x, mid as int);
            }
            high = mid;
        } else {
            return mid as i32;
        }
    }

    return -1;
}
// </vc-code>

}
fn main() {}