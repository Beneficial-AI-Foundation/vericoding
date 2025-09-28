use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
use vstd::prelude::*;
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
    // Initialize low and high
    let mut low: i32 = 0;
    let mut high: i32 = (a.len() as i32) - 1;

    // Proof that initial bounds hold
    proof!{
        assert(0 <= low <= high <= (a@.len()) - 1);
    };

    // Assert the initial invariant for key location
    proof!{
        assert(forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key ==> low <= k && k <= high);
    };

    while low <= high
        invariant
            0 <= low <= high <= (a.len() as int) - 1,
            forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key ==> low <= k && k <= high,
    {
        // Compute mid
        let mid: i32 = low + (high - low) / 2;

        // Proof that mid is within bounds
        proof!{
            assert(0 <= mid as int);
            assert(mid as int < a@.len());
        };

        // Access a[mid]
        let mid_val = a[mid as usize];

        if mid_val == key {
            // Found the key, return mid
            return mid;
        } else if mid_val < key {
            // Key is in the right half
            let old_low = low;
            let old_high = high;
            let old_mid = mid;
            proof!{
                // Since the array is sorted, if a@[mid] < key, then any key in [old_low..=old_mid] would be <= a@[mid] < key, contradiction
                assert(forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key && k <= (old_mid as int) ==> false);
                // Therefore, if key exists, it must be in [old_mid+1 .. old_high]
                assert(forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key ==> (old_mid as int + 1) <= k && k <= (old_high as int));
            };
            low = mid + 1;
        } else {
            // Key is in the left half
            let old_low = low;
            let old_high = high;
            let old_mid = mid;
            proof!{
                // Since the array is sorted, if a@[mid] > key, then any key in [old_mid..=old_high] would be >= a@[mid] > key, contradiction
                assert(forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key && k >= (old_mid as int) ==> false);
                // Therefore, if key exists, it must be in [old_low .. old_mid-1]
                assert(forall |k: int| 0 <= k < (a@.len()) && a@[k as usize] == key ==> (old_low as int) <= k && k <= (old_mid as int - 1));
            };
            high = mid - 1;
        }
    }

    // After loop, key not found
    proof!{
        // Since low > high, and invariant holds, no k satisfies the condition
        assert(forall |k: int| 0 <= k < (a@.len()) ==> a@[k as usize] != key);
    };
    -1
}
// </vc-code>

fn main() {
}

}