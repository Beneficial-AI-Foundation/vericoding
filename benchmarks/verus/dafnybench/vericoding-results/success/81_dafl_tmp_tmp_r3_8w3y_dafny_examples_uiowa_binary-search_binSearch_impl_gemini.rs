// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bin_search(a: &[int], k: int) -> (b: bool)
    requires is_sorted(a)
    ensures b == exists|i: int| 0 <= i < a.len() && a[i] == k
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed spec indexing and proof logic */
    let mut low: usize = 0;
    let mut high: usize = a.len();
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            is_sorted(a),
            forall|i: int| 0 <= i < a.len() && a@[i] == k ==> (low as int) <= i < (high as int),
        decreases (high - low) as nat
    {
        let mid: usize = low + (high - low) / 2;
        assert(low <= mid < high);

        if a[mid] < k {
            proof {
                assert forall|i: int| 0 <= i < a.len() && a@[i] == k implies (mid as int) < i by {
                    if 0 <= i < a.len() && a@[i] == k && i <= (mid as int) {
                        assert(is_sorted(a));
                        assert(a@[i] <= a@[mid as int]);
                        assert(k <= a@[mid as int]);
                        assert(false);
                    }
                }
            }
            low = mid + 1;
        } else if a[mid] > k {
            proof {
                assert forall|i: int| 0 <= i < a.len() && a@[i] == k implies i < (mid as int) by {
                    if 0 <= i < a.len() && a@[i] == k && i >= (mid as int) {
                        assert(is_sorted(a));
                        assert(a@[mid as int] <= a@[i]);
                        assert(a@[mid as int] <= k);
                        assert(false);
                    }
                }
            }
            high = mid;
        } else { // a[mid] == k
            assert(a@[mid as int] == k);
            assert(exists|i: int| 0 <= i < a.len() && a@[i] == k);
            return true;
        }
    }
    
    assert forall|i: int| 0 <= i < a.len() && a@[i] == k implies false by {
        if 0 <= i < a.len() && a@[i] == k {
            assert((low as int) <= i < (high as int));
            assert(low >= high);
            assert((low as int) >= (high as int));
            assert(false);
        }
    };
    assert(!exists|i: int| 0 <= i < a.len() && a@[i] == k);

    return false;
}
// </vc-code>

}
fn main() {}