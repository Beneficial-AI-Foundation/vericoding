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
        
        // Access the array element using spec_index directly
        let mid_val = a.spec_index(mid);
        
        if mid_val < x {
            // Use monotonicity to prove all elements from 0 to mid are < x
            assert(forall|r: int| 0 <= r <= mid ==> a.spec_index(r) <= a.spec_index(mid)) by {
                assert(forall|r: int| 0 <= r <= mid ==> r <= mid);
                // Use the sorted property
                assert(forall|r: int| 0 <= r <= mid ==> a.spec_index(r) <= a.spec_index(mid));
            };
            
            low = mid + 1;
        } else {
            // Use monotonicity to prove all elements from mid to 999 are >= x
            assert(forall|r: int| mid <= r < 1000 ==> a.spec_index(mid) <= a.spec_index(r)) by {
                assert(forall|r: int| mid <= r < 1000 ==> mid <= r);
                // Use the sorted property
                assert(forall|r: int| mid <= r < 1000 ==> a.spec_index(mid) <= a.spec_index(r));
            };
            
            high = mid;
        }
    }
    
    low
}

}