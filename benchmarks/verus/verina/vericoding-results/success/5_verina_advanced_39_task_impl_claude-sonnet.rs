// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause for the while loop */
    let mut max_val = lst[0];
    let mut idx = 1;
    
    while idx < lst.len()
        invariant
            0 < idx <= lst.len(),
            exists|i: int| 0 <= i < idx && lst[i] == max_val,
            forall|i: int| 0 <= i < idx ==> lst[i] <= max_val,
        decreases lst.len() - idx
    {
        if lst[idx] > max_val {
            max_val = lst[idx];
        }
        idx += 1;
    }
    
    max_val
}
// </vc-code>

}
fn main() {}