use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
// No helper definitions needed.
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
    let n: int = a.len() as int;
    let mut lo: int = 0;
    let mut hi: int = (a.len() - 1) as int;

    // Loop invariant:
    //  - 0 <= lo <= a.len()
    //  - -1 <= hi < a.len()
    //  - If key exists in the array, its index is within [lo, hi].
    while lo <= hi
        invariant 0 <= lo && lo <= a.len()
        invariant -1 <= hi && hi < a.len()
        invariant forall|k: int| 0 <= k < a.len() && a[k] == key ==> lo <= k && k <= hi
        decreases (hi - lo + 1) as nat
    {
        let mid: int = lo + (hi - lo) / 2;
        // mid is between lo and hi, hence valid index
        assert(mid >= 0 && mid < a.len());

        let amid: int = a[mid as usize];

        if amid == key {
            return mid as i32;
        } else if amid < key {
            // Show that any occurrence of key must be > mid, so new lo = mid+1 maintains invariant
            proof {
                // Take arbitrary k satisfying the antecedent of the invariant
                // From previous invariant we know lo <= k <= hi.
                // If k <= mid then sorted property implies a[k] <= a[mid] < key, contradiction.
                assert(forall|k: int|
                    0 <= k < a.len() && a[k] == key && k <= mid ==> false
                );
                // Therefore any such k must satisfy k >= mid+1
                assert(forall|k: int|
                    0 <= k < a.len() && a[k] == key ==> mid + 1 <= k
                );
            }
            lo = mid + 1;
        } else {
            // amid > key, so any occurrence of key must be < mid, so new hi = mid-1 maintains invariant
            proof {
                assert(forall|k: int|
                    0 <= k < a.len() && a[k] == key && k >= mid ==> false
                );
                assert(forall|k: int|
                    0 <= k < a.len() && a[k] == key ==> k <= mid - 1
                );
            }
            hi = mid - 1;
        }
    }

    // When loop exits, lo > hi. From the invariant, any k with a[k]==key must satisfy lo <= k <= hi,
    // which is impossible, so no such k exists.
    -1
}
// </vc-code>

fn main() {
}

}