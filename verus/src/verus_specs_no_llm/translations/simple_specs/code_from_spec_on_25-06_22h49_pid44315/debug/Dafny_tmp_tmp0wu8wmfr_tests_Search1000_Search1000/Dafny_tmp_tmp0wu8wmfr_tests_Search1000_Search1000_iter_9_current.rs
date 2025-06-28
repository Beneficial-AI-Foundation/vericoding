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
        
        // Convert mid to usize for array access
        let mid_usize = mid as usize;
        
        // Prove that mid_usize is within bounds
        assert(mid_usize < a.len());
        
        // Access the array element using usize indexing
        let mid_val = a[mid_usize];
        
        // Establish that mid_val equals a.spec_index(mid)
        assert(mid_val == a.spec_index(mid));
        
        if mid_val < x {
            // Prove that all elements from low to mid are < x
            assert(forall|r: int| low <= r <= mid ==> a.spec_index(r) < x) by {
                forall|r: int| low <= r <= mid implies a.spec_index(r) < x by {
                    if low <= r <= mid {
                        // By sorted property: a[r] <= a[mid]
                        if r < mid {
                            assert(a.spec_index(r) <= a.spec_index(mid));
                        } else {
                            // r == mid
                            assert(a.spec_index(r) == a.spec_index(mid));
                        }
                        // and a[mid] < x
                        assert(a.spec_index(mid) < x);
                        // so a[r] < x
                        assert(a.spec_index(r) < x);
                    }
                }
            };
            
            low = mid + 1;
        } else {
            // mid_val >= x, so all elements from mid onwards are >= x
            assert(forall|r: int| mid <= r < 1000 ==> a.spec_index(r) >= x) by {
                forall|r: int| mid <= r < 1000 implies a.spec_index(r) >= x by {
                    if mid <= r < 1000 {
                        // By sorted property: a[mid] <= a[r]
                        if mid < r {
                            assert(a.spec_index(mid) <= a.spec_index(r));
                        } else {
                            // r == mid
                            assert(a.spec_index(r) == a.spec_index(mid));
                        }
                        // and a[mid] >= x
                        assert(a.spec_index(mid) >= x);
                        // so a[r] >= x
                        assert(a.spec_index(r) >= x);
                    }
                }
            };
            
            high = mid;
        }
    }
    
    low
}

}