use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if l.len() <= 1 {
        return true;
    }
    
    let mut is_increasing = true;
    let mut is_decreasing = true;
    let mut i: usize = 0;
    
    while i < l.len() - 1
        invariant
            i < l.len(),
            is_increasing ==> (forall|k: int| #[trigger] (l@[k], l@[k + 1]) 0 <= k < i as int ==> l@[k] <= l@[k + 1]),
            is_decreasing ==> (forall|k: int| #[trigger] (l@[k], l@[k + 1]) 0 <= k < i as int ==> l@[k] >= l@[k + 1]),
        decreases l.len() - 1 - i
    {
        if l[i] > l[i + 1] {
            is_increasing = false;
        }
        if l[i] < l[i + 1] {
            is_decreasing = false;
        }
        i = i + 1;
    }
    
    is_increasing || is_decreasing
}
// </vc-code>

}
fn main() {}