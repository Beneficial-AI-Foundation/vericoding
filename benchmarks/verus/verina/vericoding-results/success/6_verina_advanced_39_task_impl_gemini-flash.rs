// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes needed for helper helper, but removed comment as it's not the initial submission of helper code (only relevant for the first turn) */
proof fn greater_than_or_equal_to_all(lst: &Vec<usize>, val: usize) -> (result: bool)
{
    forall |i: int| 0 <= i && (i as nat) < lst.len() ==> lst[i] <= val
}
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added decreases clause to the while loop */
{
    let mut max_val = lst[0];
    let mut i: usize = 1;
    while i < lst.len()
        invariant
            0 < lst.len(),
            0 < i,
            i <= lst.len(),
            forall|j: int| 0 <= j && (j as nat) < i ==> lst[j] <= max_val,
            exists|k: int| 0 <= k as int && (k as nat) < i && lst[k] == max_val,
        decreases lst.len() - i
    {
        if lst[i] > max_val {
            max_val = lst[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}