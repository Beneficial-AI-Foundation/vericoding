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
    let mut max = lst[0];
    let mut i: usize = 1;

    while i < lst.len()
        invariant
            1 <= i <= lst.len(),
            exists|k: int| 0 <= k < i && lst.spec_index(k) == max,
            forall|k: int| 0 <= k < i ==> lst.spec_index(k) <= max,
        decreases lst.len() - i
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