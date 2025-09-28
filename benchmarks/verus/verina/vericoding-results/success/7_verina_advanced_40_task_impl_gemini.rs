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
    let mut i = 1;
    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            exists|j: int| 0 <= j < i && lst[j] == max,
            forall|k: int| 0 <= k < i ==> lst[k] <= max,
        decreases lst.len() - i,
    {
        if lst[i] > max {
            max = lst[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}