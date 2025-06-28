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
    
    if a[mid as usize] == x {
        return mid;
    } else {
        return SearchRecursive(a, i, mid, x);
    }
}

}