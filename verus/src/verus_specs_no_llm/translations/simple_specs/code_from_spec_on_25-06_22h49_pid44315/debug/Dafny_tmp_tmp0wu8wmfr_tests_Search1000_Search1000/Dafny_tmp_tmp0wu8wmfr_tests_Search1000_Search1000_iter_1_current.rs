use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Search1000(a: Vec<int>, x: int) -> (k: int)
    requires
        a.len() >= 1000,
        forall p,q | 0 <= p < q < 1000 :: a.spec_index(p) <= a.spec_index(q)
    ensures
        0 <= k <= 1000,
        forall r | 0 <= r < k :: a.spec_index(r) < x,
        forall r | k <= r < 1000 :: a.spec_index(r) >= x
{
    let mut low = 0;
    let mut high = 1000;
    
    while low < high
        invariant
            0 <= low <= high <= 1000,
            forall r | 0 <= r < low :: a.spec_index(r) < x,
            forall r | high <= r < 1000 :: a.spec_index(r) >= x
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    low
}

}