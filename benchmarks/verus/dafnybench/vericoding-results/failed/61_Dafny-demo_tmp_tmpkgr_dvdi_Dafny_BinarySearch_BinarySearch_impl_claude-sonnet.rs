use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
// Helper lemma to prove that if an element is not found in a sorted array,
// it doesn't exist anywhere in the array
proof fn lemma_binary_search_not_found(a: &[int], key: int, low: int, high: int)
    requires
        sorted(a, 0, (a.len() - 1) as int),
        0 <= low <= a.len(),
        -1 <= high < a.len(),
        low > high,
        forall|i: int| 0 <= i < low ==> a[i] < key,
        forall|i: int| high < i < a.len() ==> a[i] > key,
    ensures
        forall|k: int| 0 <= k < a.len() ==> a[k] != key,
{
    assert forall|k: int| 0 <= k < a.len() implies a[k] != key by {
        if 0 <= k < low {
            assert(a[k] < key);
        } else if high < k < a.len() {
            assert(a[k] > key);
        } else {
            // low <= k <= high, but low > high, so this case is impossible
            assert(false);
        }
    };
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
    let mut low: i32 = 0;
    let mut high: i32 = if a.len() <= i32::MAX as usize {
        (a.len() - 1) as i32
    } else {
        i32::MAX
    };
    
    // Ensure preconditions for the loop
    assert(a.len() > 0);
    assert(high >= 0);
    assert(high < a.len());
    
    while low <= high
        invariant
            0 <= low <= a.len(),
            -1 <= high < a.len(),
            sorted(a, 0, (a.len() - 1) as int),
            forall|i: int| 0 <= i < low ==> a[i] < key,
            forall|i: int| high < i < a.len() ==> a[i] > key,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid <= high);
        assert(0 <= mid < a.len());
        
        if a[mid as usize] == key {
            return mid;
        } else if a[mid as usize] < key {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    proof {
        lemma_binary_search_not_found(a, key, low as int, high as int);
    }
    
    -1
}
// </vc-code>

fn main() {
}

}