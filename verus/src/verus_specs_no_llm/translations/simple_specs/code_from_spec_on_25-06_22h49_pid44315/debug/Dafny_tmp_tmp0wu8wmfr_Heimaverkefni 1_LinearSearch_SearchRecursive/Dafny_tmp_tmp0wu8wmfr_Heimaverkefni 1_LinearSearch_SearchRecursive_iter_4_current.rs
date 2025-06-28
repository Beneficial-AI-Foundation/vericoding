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
    
    // Since j <= a.len() and mid = j - 1, we have mid < a.len()
    // Since i < j (from i >= j being false), we have i <= mid
    assert(mid < a.len());
    assert(i <= mid);
    assert(mid < j);
    
    if a.spec_index(mid) == x {
        return mid;
    } else {
        let result = SearchRecursive(a, i, mid, x);
        
        // Help verification understand the properties
        if result != -1 {
            assert(a.spec_index(result) == x);
            assert(forall |r| result < r < mid :: a.spec_index(r) != x);
            // Extend the property to include mid
            assert(forall |r| result < r < j :: a.spec_index(r) != x) by {
                assert(forall |r| result < r < mid :: a.spec_index(r) != x);
                assert(mid < j);
                assert(a.spec_index(mid) != x);
                assert(forall |r| result < r < j :: {
                    if r < mid {
                        a.spec_index(r) != x
                    } else if r == mid {
                        a.spec_index(r) != x
                    } else {
                        true // r >= j is impossible since r < j
                    }
                });
            }
        } else {
            assert(forall |r| i <= r < mid :: a.spec_index(r) != x);
            // Extend to include mid
            assert(forall |r| i <= r < j :: a.spec_index(r) != x) by {
                assert(forall |r| i <= r < mid :: a.spec_index(r) != x);
                assert(a.spec_index(mid) != x);
                assert(mid < j);
                assert(forall |r| i <= r < j :: {
                    if r < mid {
                        a.spec_index(r) != x
                    } else if r == mid {
                        a.spec_index(r) != x
                    } else {
                        true // r >= j is impossible since r < j
                    }
                });
            }
        }
        
        return result;
    }
}

}