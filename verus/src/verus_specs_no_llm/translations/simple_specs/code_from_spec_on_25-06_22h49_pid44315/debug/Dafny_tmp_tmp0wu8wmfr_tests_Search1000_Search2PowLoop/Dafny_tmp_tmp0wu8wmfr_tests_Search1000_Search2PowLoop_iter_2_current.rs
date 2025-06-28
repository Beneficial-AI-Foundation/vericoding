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
        0 <= i <= i + n <= a.len(),
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
    {
        let mid = left + (right - left) / 2;
        
        assert(i <= mid < i + n);
        
        if a[mid] < x {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    left
}

}