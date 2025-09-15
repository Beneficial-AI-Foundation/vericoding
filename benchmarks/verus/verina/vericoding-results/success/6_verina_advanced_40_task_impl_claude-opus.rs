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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut max = lst[0];
    let mut max_idx = 0;
    
    let mut i = 1;
    while i < lst.len()
        invariant
            0 <= max_idx < i <= lst.len(),
            lst[max_idx as int] == max,
            forall|j: int| 0 <= j < i ==> lst[j] <= max,
        decreases lst.len() - i,
    {
        if lst[i] > max {
            max = lst[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    max
}
// </vc-code>

}
fn main() {}