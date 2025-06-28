use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SearchRecursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        i <= k < j || k == -1,
        k != -1 ==> a.spec_index(k) == x,
        k != -1 ==> forall |r| k < r < j :: a.spec_index(r) != x,
        k == -1 ==> forall |r| i <= r < j :: a.spec_index(r) != x
    decreases j - i
{
    if i >= j {
        return -1;
    }
    
    let mid = j - 1;
    
    // Add assertion to help verification
    assert(0 <= mid < a.len());
    assert(i <= mid < j);
    
    if a.spec_index(mid) == x {
        return mid;
    } else {
        let result = SearchRecursive(a, i, mid, x);
        
        // Help verification understand the properties
        if result != -1 {
            assert(a.spec_index(result) == x);
            assert(forall |r| result < r < mid :: a.spec_index(r) != x);
            assert(forall |r| result < r < j :: a.spec_index(r) != x) by {
                assert(mid < j);
                assert(a.spec_index(mid) != x);
            }
        } else {
            assert(forall |r| i <= r < mid :: a.spec_index(r) != x);
            assert(forall |r| i <= r < j :: a.spec_index(r) != x) by {
                assert(a.spec_index(mid) != x);
            }
        }
        
        return result;
    }
}

}