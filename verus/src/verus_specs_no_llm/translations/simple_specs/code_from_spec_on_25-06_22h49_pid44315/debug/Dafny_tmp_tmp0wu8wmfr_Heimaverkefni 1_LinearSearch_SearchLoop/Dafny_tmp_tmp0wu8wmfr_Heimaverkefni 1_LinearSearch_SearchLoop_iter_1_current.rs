// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SearchLoop(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        i <= k < j || k == -1,
        k != -1 ==> a.spec_index(k) == x,
        k != -1 ==> forall r | k < r < j :: a.spec_index(r) != x,
        k == -1 ==> forall r | i <= r < j :: a.spec_index(r) != x
{
    let mut pos = j - 1;
    
    while pos >= i
        invariant
            i <= pos + 1 <= j,
            forall r | pos < r < j :: a.spec_index(r) != x
    {
        if a.spec_index(pos) == x {
            return pos;
        }
        pos = pos - 1;
    }
    
    return -1;
}

}