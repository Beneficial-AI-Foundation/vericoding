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
        forall|p: int, q: int| i <= p < q < i + n ==> a.spec_index(p) <= a.spec_index(q),
        Is2Pow((n + 1) as int)
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k ==> a.spec_index(r) < x,
        forall|r: int| k <= r < i + n ==> a.spec_index(r) >= x
{
    let mut left = i;
    let mut right = i + n;
    
    while left < right
        invariant
            i <= left <= right <= i + n,
            forall|r: int| i <= r < left ==> a.spec_index(r) < x,
            forall|r: int| right <= r < i + n ==> a.spec_index(r) >= x
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        assert(left < right);
        assert(left <= mid < right) by {
            assert(mid == left + (right - left) / 2);
            assert((right - left) / 2 < right - left);
            assert(mid < left + (right - left));
            assert(mid < right);
            assert((right - left) / 2 >= 0);
            assert(mid >= left);
        }
        
        if a[mid] < x {
            assert(forall|r: int| i <= r <= mid ==> a.spec_index(r) < x) by {
                assert(a.spec_index(mid) < x);
                assert(forall|r: int| i <= r < left ==> a.spec_index(r) < x);
                assert(forall|r: int| left <= r <= mid ==> a.spec_index(r) <= a.spec_index(mid));
            }
            left = mid + 1;
        } else {
            assert(forall|r: int| mid <= r < i + n ==> a.spec_index(r) >= x) by {
                assert(a.spec_index(mid) >= x);
                assert(forall|r: int| right <= r < i + n ==> a.spec_index(r) >= x);
                assert(forall|r: int| mid <= r < right ==> a.spec_index(r) >= a.spec_index(mid));
            }
            right = mid;
        }
    }
    
    assert(left == right);
    assert(forall|r: int| i <= r < left ==> a.spec_index(r) < x);
    assert(forall|r: int| left <= r < i + n ==> a.spec_index(r) >= x);
    
    left
}

}