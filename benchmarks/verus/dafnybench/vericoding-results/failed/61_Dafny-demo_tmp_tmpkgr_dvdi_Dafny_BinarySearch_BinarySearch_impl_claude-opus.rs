use vstd::prelude::*;

verus! {

// Predicate to check if array slice is sorted
spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut lo: usize = 0;
    let mut hi: usize = a.len() - 1;
    
    while lo <= hi
        invariant
            0 <= lo <= a.len(),
            hi < a.len(),
            sorted(a, 0, (a.len() - 1) as int),
            forall|k: int| 0 <= k < lo ==> #[trigger] a[k] < key,
            forall|k: int| hi < k < a.len() ==> #[trigger] a[k] > key,
            lo > hi ==> forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != key,
        decreases hi - lo + 1,
    {
        let mid: usize = lo + (hi - lo) / 2;
        
        if a[mid] == key {
            assert(0 <= mid < a.len());
            assert(a[mid as int] == key);
            return mid as i32;
        } else if a[mid] < key {
            assert(forall|k: int| 0 <= k <= mid ==> #[trigger] a[k] < key || a[k] == a[mid as int]);
            assert(a[mid as int] < key);
            assert(forall|k: int| 0 <= k <= mid ==> #[trigger] a[k] <= a[mid as int] || k == mid);
            assert(forall|k: int| 0 <= k <= mid ==> #[trigger] a[k] <= key);
            
            if mid == hi {
                assert(lo == hi);
                assert(a[hi as int] < key);
                assert(forall|k: int| 0 <= k <= hi ==> #[trigger] a[k] != key);
                assert(forall|k: int| hi < k < a.len() ==> #[trigger] a[k] != key);
                assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != key);
                return -1;
            }
            lo = mid + 1;
        } else {
            assert(a[mid as int] > key);
            assert(forall|k: int| mid <= k < a.len() ==> #[trigger] a[k] >= a[mid as int]);
            assert(forall|k: int| mid <= k < a.len() ==> #[trigger] a[k] > key || a[k] == a[mid as int]);
            assert(forall|k: int| mid <= k < a.len() ==> #[trigger] a[k] >= key);
            
            if mid == 0 {
                assert(lo == 0);
                assert(a[0] > key);
                assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] >= a[0]);
                assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != key);
                return -1;
            }
            hi = mid - 1;
        }
    }
    
    assert(lo > hi);
    assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != key);
    -1
}
// </vc-code>

fn main() {
}

}