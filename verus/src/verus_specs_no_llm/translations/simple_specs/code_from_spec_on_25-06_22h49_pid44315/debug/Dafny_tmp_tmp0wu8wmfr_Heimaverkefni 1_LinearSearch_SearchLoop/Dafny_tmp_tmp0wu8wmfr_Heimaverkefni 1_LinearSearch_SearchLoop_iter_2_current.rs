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
            i - 1 <= pos < j,
            forall|r| pos < r < j ==> a.spec_index(r) != x
    {
        if a.spec_index(pos) == x {
            return pos;
        }
        pos = pos - 1;
    }
    
    return -1;
}

}

The key changes I made:




The algorithm works as follows:
- It searches backwards from `j-1` to `i`
- If it finds `x` at position `pos`, it returns `pos`, and the invariant guarantees that no element at positions `pos+1` to `j-1` equals `x` (satisfying the "rightmost occurrence" property)
- If it doesn't find `x` anywhere, it returns `-1`, and the invariant (when the loop exits with `pos < i`) guarantees that no element from `i` to `j-1` equals `x`

This implementation satisfies all the postconditions:
- The return value is either in range `[i, j)` or `-1`
- If we return a valid index, that element equals `x`
- If we return a valid index, it's the rightmost occurrence of `x` in the range
- If we return `-1`, no element in the range equals `x`