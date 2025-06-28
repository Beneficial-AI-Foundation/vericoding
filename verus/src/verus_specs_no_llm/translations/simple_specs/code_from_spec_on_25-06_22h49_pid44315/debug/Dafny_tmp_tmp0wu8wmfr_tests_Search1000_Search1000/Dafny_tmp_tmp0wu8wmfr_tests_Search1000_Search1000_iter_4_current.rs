use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Search1000(a: Vec<int>, x: int) -> (k: int)
    requires
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a.spec_index(p) <= a.spec_index(q)
    ensures
        0 <= k <= 1000,
        forall|r: int| 0 <= r < k ==> a.spec_index(r) < x,
        forall|r: int| k <= r < 1000 ==> a.spec_index(r) >= x
{
    let mut low: int = 0;
    let mut high: int = 1000;
    
    while low < high
        invariant
            0 <= low <= high <= 1000,
            forall|r: int| 0 <= r < low ==> a.spec_index(r) < x,
            forall|r: int| high <= r < 1000 ==> a.spec_index(r) >= x
    {
        let mid = low + (high - low) / 2;
        
        // Prove bounds for mid
        assert(low <= mid < high);
        assert(0 <= mid < 1000);
        assert(mid < a.len());
        
        // Access the array element - convert int to usize for indexing
        let mid_usize = mid as usize;
        let mid_val = a[mid_usize];
        
        // Establish the relationship between indexed value and spec_index
        assert(a.spec_index(mid) == a[mid_usize]);
        
        if mid_val < x {
            // Prove that a.spec_index(mid) < x before updating low
            assert(a.spec_index(mid) < x);
            // Prove that all elements from 0 to mid are < x
            assert(forall|r: int| 0 <= r <= mid ==> a.spec_index(r) < x);
            low = mid + 1;
        } else {
            // Prove that a.spec_index(mid) >= x before updating high
            assert(a.spec_index(mid) >= x);
            // Prove that all elements from mid to 999 are >= x
            assert(forall|r: int| mid <= r < 1000 ==> a.spec_index(r) >= x);
            high = mid;
        }
    }
    
    low
}

}