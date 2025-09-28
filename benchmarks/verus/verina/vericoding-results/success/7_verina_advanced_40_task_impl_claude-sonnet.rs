// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: Vec<i32>) -> (result: i32)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    let mut max = lst[0];
    let mut idx = 1;
    
    while idx < lst.len()
        invariant
            0 < idx <= lst.len(),
            exists|i: int| 0 <= i < idx && lst[i] == max,
            forall|i: int| 0 <= i < idx ==> lst[i] <= max,
        decreases lst.len() - idx
    {
        if lst[idx] > max {
            max = lst[idx];
        }
        idx += 1;
    }
    
    max
}
// </vc-code>

}
fn main() {}