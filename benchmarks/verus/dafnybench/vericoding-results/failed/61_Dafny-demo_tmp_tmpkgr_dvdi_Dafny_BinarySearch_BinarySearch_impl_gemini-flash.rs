use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
spec fn sorted_segment(a: &[int], lo: int, hi: int) -> bool {
    forall|i: int, j: int| lo <= i <= j <= hi < a.len() ==> a[i] <= a[j]
}

proof fn lemma_sorted_implies_sorted_segment(a: &[int], l: int, u: int)
    requires sorted(a, l, u),
    ensures forall|lo: int, hi: int| l <= lo <= hi <= u ==> sorted_segment(a, lo, hi),
{
    assert forall|lo: int, hi: int| l <= lo <= hi <= u implies sorted_segment(a, lo, hi) by {
        assert forall|i: int, j: int| lo <= i <= j <= hi < a.len() implies a[i] <= a[j] by {
            // This follows directly from the definition of sorted(a, l, u)
            // since l <= lo <= i <= j <= hi <= u
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], key: int) -> (index: i32)
    requires 
        a.len() > 0,
        sorted(a, 0, (a.len() - 1) as int),
    ensures 
        index >= 0 ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut low: int = 0;
    let mut high: int = (a.len() - 1) as int;
    let mut result: i32 = -1;

    proof {
        lemma_sorted_implies_sorted_segment(a, 0, (a.len() - 1) as int);
    }

    while low <= high
        invariant
            0 <= low,
            high < a.len() as int,
            forall|k: int| 0 <= k < a.len() && k < low ==> a[k] != key,
            forall|k: int| 0 <= k < a.len() && k > high ==> a[k] != key,
            sorted(a, 0, (a.len() - 1) as int),
            sorted_segment(a, low, high), // The segment a[low..high] is sorted
    {
        let mid: int = low + (high - low) / 2;
        assert(low <= mid && mid <= high); // mid is within [low, high]

        if a[mid] == key {
            result = mid as i32;
            low = high + 1; // Terminate loop
        } else if a[mid] < key {
            // Key is in the upper half or not present
            // All elements a[k'] for k' <= mid are less than key
            // So these can be excluded from the search space
            let old_low = low; // Store old_low for assertion
            low = mid + 1;

            assert forall|k: int| (old_low <= k && k <= mid) ==> a[k] != key by {
                assert(sorted_segment(a, old_low, high)); // Use 'high' from the invariant
                assert(a[mid] < key);
                assert forall |k_inner:int| (old_low <= k_inner && k_inner <= mid) implies a[k_inner] <= a[mid] by {
                    assert(sorted_segment(a, old_low, mid)); // This segment is sorted
                };
                assert forall |k_inner:int| (old_low <= k_inner && k_inner <= mid) implies (a[k_inner] <= a[mid]) implies a[k_inner] != key
                by {
                    assert(a[mid] < key);
                    if a[k_inner] == key {
                        assert(key <= a[mid]); // From a[k_inner] <= a[mid]
                        assert(false); // Contradiction: key < key
                    }
                };
            }
        } else {
            // Key is in the lower half or not present
            // All elements a[k'] for k' >= mid are greater than key
            // So these can be excluded from the search space
            let old_high = high; // Store old_high for assertion
            high = mid - 1;

            assert forall|k: int| (mid <= k && k <= old_high) ==> a[k] != key by {
                assert(sorted_segment(a, low, old_high)); // Use 'low' from the invariant
                assert(a[mid] > key);
                assert forall |k_inner:int| (mid <= k_inner && k_inner <= old_high) implies a[k_inner] >= a[mid] by {
                    assert(sorted_segment(a, mid, old_high)); // This segment is sorted
                };
                assert forall |k_inner:int| (mid <= k_inner && k_inner <= old_high) implies (a[k_inner] >= a[mid]) implies a[k_inner] != key
                by {
                    assert(a[mid] > key);
                    if a[k_inner] == key {
                        assert(key >= a[mid]); // From a[k_inner] >= a[mid]
                        assert(false); // Contradiction: key > key
                    }
                };
            }
        }
    }

    if result >= 0 {
        assert(result < a.len() as int);
        assert(a[result as int] == key);
    } else {
        // If result is still -1, it means the element was not found.
        // The loop terminated because low > high.
        // The loop invariant ensures that elements outside [low, high] (which is now empty)
        // do not contain the key.
        assert forall|k: int| 0 <= k < a.len() ==> a[k] != key by {
            if low > high {
                // The loop invariant states:
                // forall|k: int| 0 <= k < a.len() && k < low ==> a[k] != key,
                // forall|k: int| 0 <= k < a.len() && k > high ==> a[k] != key,
                // Since low > high, there are no k such that low <= k <= high.
                // So, any k in the array is either k < low or k > high.
                // Thus forall k, a[k] != key.
            }
        }
    }
    result
}
// </vc-code>

fn main() {
}

}