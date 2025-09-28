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
    /* code modified by LLM (iteration 3): Added existential invariant to ensure postcondition holds by witnessing that max_val equals some list element */
    let mut max_val: usize = lst[0];
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            1 <= (i as int) <= (lst.len() as int),
            forall|j: int| 0 <= j < (i as int) ==> (lst@[j] as int) <= (max_val as int),
            exists|k: int| 0 <= k < (i as int) && max_val == lst@[k],
        decreases (lst.len() - i) as int
    {
        max_val = if lst[i] > max_val { lst[i] } else { max_val };
        i += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}