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
    let mut pos = j - 1;
    
    while pos >= i
        invariant
            i - 1 <= pos <= j - 1,
            forall|r| pos < r < j ==> a.spec_index(r) != x
        decreases pos - i + 1
    {
        if a.spec_index(pos) == x {
            return pos;
        }
        pos = pos - 1;
    }
    
    return -1;
}

}

The key fixes:



   - Returns either a valid index in `[i, j)` or `-1`
   - If returning a valid index, that element equals `x`
   - If returning a valid index, it's the rightmost occurrence (no element to the right equals `x`)
   - If returning `-1`, no element in the range equals `x`

The algorithm searches backwards from `j-1` to `i`, maintaining the invariant that all elements to the right of the current position don't equal `x`. This ensures we find the rightmost occurrence if it exists.