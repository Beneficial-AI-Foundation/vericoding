use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Is2Pow(n: int) -> bool 
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && Is2Pow(n / 2)
    }
}

fn Search2PowLoop(a: Vec<int>, i: usize, n: usize, x: int) -> (k: usize)
    requires
        0 <= i && i + n <= a.len(),
        forall p, q | i <= p < q < i + n :: a.spec_index(p) <= a.spec_index(q),
        Is2Pow((n + 1) as int)
    ensures
        i <= k <= i + n,
        forall r | i <= r < k :: a.spec_index(r) < x,
        forall r | k <= r < i + n :: a.spec_index(r) >= x
{
    let mut left = i;
    let mut right = i + n;
    
    while left < right
        invariant
            i <= left <= right <= i + n,
            forall r | i <= r < left :: a.spec_index(r) < x,
            forall r | right <= r < i + n :: a.spec_index(r) >= x
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if a[mid] < x {
            left = mid + 1;
            
            // Prove the invariant is maintained for the left case
            assert(forall r | i <= r < left :: a.spec_index(r) < x) by {
                // The old left maintained the invariant
                assert(forall r | i <= r < mid + 1 - 1 :: a.spec_index(r) < x);
                // We know a[mid] < x
                assert(a.spec_index(mid) < x);
                // So all elements up to the new left (mid + 1) are < x
            }
        } else {
            right = mid;
            
            // Prove the invariant is maintained for the right case  
            assert(forall r | right <= r < i + n :: a.spec_index(r) >= x) by {
                // We know a[mid] >= x
                assert(a.spec_index(mid) >= x);
                // By sortedness, all elements from mid onwards are >= x
                assert(forall r | mid <= r < i + n :: a.spec_index(r) >= x) by {
                    // This follows from the sortedness precondition
                }
            }
        }
    }
    
    left
}

}