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
        k != -1 ==> forall|r| k < r < j ==> a.spec_index(r) != x,
        k == -1 ==> forall|r| i <= r < j ==> a.spec_index(r) != x
{
    if i == j {
        return -1;
    }
    
    let mut pos = j - 1;
    
    while pos >= i
        invariant
            i - 1 <= pos < j,
            forall|r| pos < r < j ==> a.spec_index(r) != x
        decreases pos - i + 1
    {
        if a.spec_index(pos) == x {
            // We found x at position pos
            // Need to prove that all positions after pos don't contain x
            assert(forall|r| pos < r < j ==> a.spec_index(r) != x);
            return pos;
        }
        pos = pos - 1;
    }
    
    // pos < i, so we've checked all positions from i to j-1
    assert(pos < i);
    assert(forall|r| pos < r < j ==> a.spec_index(r) != x);
    assert(forall|r| i <= r < j ==> a.spec_index(r) != x);
    return -1;
}

}