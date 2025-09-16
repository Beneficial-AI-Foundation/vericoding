// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)

    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
// </vc-spec>
// <vc-code>
{
    if l.len() <= 1 {
        return true;
    }
    
    let mut increasing = true;
    let mut decreasing = true;
    let mut i: usize = 0;
    
    while i < l.len() - 1
        invariant
            0 <= i <= l.len() - 1,
            increasing <==> (forall|j: int, k: int| 0 <= j < k <= i ==> l@[j] <= l@[k]),
            decreasing <==> (forall|j: int, k: int| 0 <= j < k <= i ==> l@[j] >= l@[k]),
        decreases l.len() - 1 - i
    {
        if l[i] > l[i + 1] {
            increasing = false;
        }
        if l[i] < l[i + 1] {
            decreasing = false;
        }
        i = i + 1;
    }
    
    increasing || decreasing
}
// </vc-code>

}
fn main() {}