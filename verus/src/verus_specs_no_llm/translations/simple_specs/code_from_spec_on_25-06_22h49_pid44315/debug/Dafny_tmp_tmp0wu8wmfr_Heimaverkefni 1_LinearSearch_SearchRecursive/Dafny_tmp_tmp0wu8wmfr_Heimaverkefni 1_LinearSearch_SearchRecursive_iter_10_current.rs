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
    
    if a.spec_index(mid) == x {
        return mid;
    } else {
        let result = SearchRecursive(a, i, mid, x);
        
        if result != -1 {
            // result is a valid index in [i, mid) where a[result] == x
            // From recursive call postcondition: forall |r| result < r < mid :: a[r] != x
            // We know a[mid] != x (from the else branch)
            // Since mid == j - 1, we need to show: forall |r| result < r < j :: a[r] != x
            assert(forall |r| result < r < mid :: a.spec_index(r) != x);
            assert(a.spec_index(mid) != x);
            assert(mid == j - 1);
            
            // Prove the postcondition by showing it holds for each possible r
            assert(forall |r| result < r < j :: a.spec_index(r) != x) by {
                assert(forall |r| result < r < j :: 
                    (result < r < mid ==> a.spec_index(r) != x) &&
                    (r == mid ==> a.spec_index(r) != x) &&
                    (r > mid ==> r >= j)
                );
            };
        } else {
            // result == -1, so no element in [i, mid) equals x
            // We also know a[mid] != x
            // So no element in [i, j) equals x
            assert(forall |r| i <= r < mid :: a.spec_index(r) != x);
            assert(a.spec_index(mid) != x);
            assert(mid == j - 1);
            
            // Prove the postcondition by showing it holds for each possible r
            assert(forall |r| i <= r < j :: a.spec_index(r) != x) by {
                assert(forall |r| i <= r < j :: 
                    (i <= r < mid ==> a.spec_index(r) != x) &&
                    (r == mid ==> a.spec_index(r) != x) &&
                    (r > mid ==> r >= j)
                );
            };
        }
        
        return result;
    }
}

}