use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn BinarySearch(a: Vec<int>, key: int) -> (n: int)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
    ensures
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a.spec_index(i) < key,
        forall|i: int| n <= i < a.len() ==> key <= a.spec_index(i)
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < key,
            forall|i: int| high <= i < a.len() ==> key <= a.spec_index(i)
    {
        let mid = low + (high - low) / 2;
        
        // Prove that mid is in bounds
        assert(low < high);
        assert(mid >= low);
        assert(mid < high);
        assert(mid < a.len());
        
        if a[mid] < key {
            low = mid + 1;
            
            // Help Verus prove the invariant for the updated low
            assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < key) by {
                // Split the range into two parts: [0, mid) and {mid}
                let old_low = (mid + 1) - 1;  // This is mid
                assert(forall|i: int| 0 <= i < old_low ==> a.spec_index(i) < key);  // From loop invariant
                assert(a.spec_index(old_low) < key);  // From the if condition
            };
        } else {
            high = mid;
            
            // Help Verus prove the invariant for the updated high
            assert(forall|i: int| high <= i < a.len() ==> key <= a.spec_index(i)) by {
                // We know key <= a[mid] from the else condition
                // For i >= mid, we use sortedness to show key <= a[i]
                assert(forall|i: int| mid <= i < a.len() ==> key <= a.spec_index(i)) by {
                    // Use the fact that key <= a[mid] and sortedness a[mid] <= a[i] for i >= mid
                    assert(key <= a.spec_index(mid as int));  // From else condition
                    assert(forall|i: int| mid <= i < a.len() ==> a.spec_index(mid as int) <= a.spec_index(i));  // From sortedness
                };
            };
        }
    }
    
    low as int
}

}