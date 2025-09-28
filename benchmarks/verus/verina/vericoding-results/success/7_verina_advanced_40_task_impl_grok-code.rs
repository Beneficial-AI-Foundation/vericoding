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
    let mut max_val = lst[0];
    let mut index = 1;
    while index < lst.len()
        invariant
            1 <= index <= lst.len(),
            forall|j: int| 0 <= j < index ==> lst@[j] <= max_val,
            exists|k: int| 0 <= k < index && lst@[k] == max_val,
        decreases (lst.len() - index)
    {
        if lst[index] > max_val {
            max_val = lst[index];
        }
        index += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}