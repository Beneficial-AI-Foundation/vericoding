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
        
        // Convert mid to usize for array access
        let mid_usize = mid as usize;
        
        // Access the array element
        let mid_val = a[mid_usize];
        
        if mid_val < x {
            // All elements from low to mid are < x
            proof {
                assert forall|r: int| low <= r <= mid implies a.spec_index(r) < x by {
                    if low <= r <= mid {
                        if r < mid {
                            // By sorted property and transitivity
                            assert(a.spec_index(r) <= a.spec_index(mid));
                            assert(a.spec_index(mid) < x);
                        } else {
                            // r == mid
                            assert(r == mid);
                            assert(a.spec_index(r) == a.spec_index(mid));
                            assert(a.spec_index(mid) < x);
                        }
                    }
                };
            }
            
            low = mid + 1;
        } else {
            // mid_val >= x, so all elements from mid onwards are >= x
            proof {
                assert forall|r: int| mid <= r < 1000 implies a.spec_index(r) >= x by {
                    if mid <= r < 1000 {
                        if mid < r {
                            // By sorted property
                            assert(a.spec_index(mid) <= a.spec_index(r));
                            assert(a.spec_index(mid) >= x);
                        } else {
                            // r == mid
                            assert(r == mid);
                            assert(a.spec_index(r) == a.spec_index(mid));
                            assert(a.spec_index(mid) >= x);
                        }
                    }
                };
            }
            
            high = mid;
        }
    }
    
    low
}

}