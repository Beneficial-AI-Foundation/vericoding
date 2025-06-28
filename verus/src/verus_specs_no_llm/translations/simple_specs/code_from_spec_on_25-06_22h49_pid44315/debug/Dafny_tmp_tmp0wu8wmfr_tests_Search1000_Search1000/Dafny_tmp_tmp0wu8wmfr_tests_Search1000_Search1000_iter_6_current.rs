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
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        // Prove bounds for mid
        assert(low <= mid < high);
        assert(0 <= mid < 1000);
        
        // Access the array element using regular indexing for executable code
        let mid_val = a[mid as usize];
        
        // Establish that mid_val equals a.spec_index(mid)
        assert(mid_val == a.spec_index(mid));
        
        if mid_val < x {
            // Prove that all elements from low to mid are < x
            assert(forall|r: int| low <= r <= mid ==> a.spec_index(r) < x) by {
                assert(forall|r: int| low <= r <= mid ==> {
                    // r <= mid, so by sorted property: a[r] <= a[mid]
                    // and a[mid] < x, so a[r] < x
                    &&& (0 <= r <= mid)
                    &&& (a.spec_index(r) <= a.spec_index(mid))
                    &&& (a.spec_index(mid) < x)
                    &&& (a.spec_index(r) < x)
                });
            };
            
            low = mid + 1;
        } else {
            // mid_val >= x, so all elements from mid onwards are >= x
            assert(forall|r: int| mid <= r < 1000 ==> a.spec_index(r) >= x) by {
                assert(forall|r: int| mid <= r < 1000 ==> {
                    // mid <= r, so by sorted property: a[mid] <= a[r]
                    // and a[mid] >= x, so a[r] >= x
                    &&& (mid <= r < 1000)
                    &&& (a.spec_index(mid) <= a.spec_index(r))
                    &&& (a.spec_index(mid) >= x)
                    &&& (a.spec_index(r) >= x)
                });
            };
            
            high = mid;
        }
    }
    
    low
}

}