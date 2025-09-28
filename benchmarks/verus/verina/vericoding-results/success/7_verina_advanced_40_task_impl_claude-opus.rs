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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut max = lst[0];
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            exists|j: int| 0 <= j < i && lst[j] == max,
            forall|j: int| 0 <= j < i ==> lst[j] <= max,
        decreases lst.len() - i,
    {
        if lst[i as usize] > max {
            max = lst[i as usize];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}