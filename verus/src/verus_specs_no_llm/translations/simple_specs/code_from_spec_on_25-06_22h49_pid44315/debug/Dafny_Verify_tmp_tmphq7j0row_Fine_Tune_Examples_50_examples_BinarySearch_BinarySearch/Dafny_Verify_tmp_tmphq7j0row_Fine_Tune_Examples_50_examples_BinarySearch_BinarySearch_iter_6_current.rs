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
                // For any i in the new range [0, low), either i was in the old range or i == mid
                assert(forall|i: int| 0 <= i < low ==> {
                    if i < mid as int {
                        a.spec_index(i) < key  // From old loop invariant
                    } else if i == mid as int {
                        a.spec_index(i) < key  // From the if condition: a[mid] < key
                    } else {
                        false  // i cannot be > mid since low = mid + 1
                    }
                });
            };
        } else {
            high = mid;
            
            // Help Verus prove the invariant for the updated high
            assert(forall|i: int| high <= i < a.len() ==> key <= a.spec_index(i)) by {
                // For any i in [high, len), either i was in the old range or i == mid
                assert(forall|i: int| high <= i < a.len() ==> {
                    if i == mid as int {
                        key <= a.spec_index(i)  // From else condition: key <= a[mid]
                    } else if i > mid as int {
                        // Use sortedness: a[mid] <= a[i] and key <= a[mid]
                        key <= a.spec_index(mid as int) && a.spec_index(mid as int) <= a.spec_index(i)
                    } else {
                        false  // i cannot be < mid since high = mid
                    }
                });
            };
        }
    }
    
    low as int
}

}