// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_first_elements(lst: Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0,
    ensures 
        result.len() == lst.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added precondition to loop invariant to prove safe indexing */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.len() == i,
            forall|k: int| 0 <= k < lst.len() ==> lst@[k].len() > 0,
            forall|j: int| 0 <= j < i as int ==> result@[j] == lst@[j]@[0],
        decreases lst.len() - i
    {
        let elem = lst[i][0];
        result.push(elem);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}