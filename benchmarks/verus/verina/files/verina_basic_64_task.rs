// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insert(oline: &Vec<char>, l: usize, nl: &Vec<char>, p: usize, at_pos: usize) -> (result: Vec<char>)
    requires
        l <= oline.len(),
        p <= nl.len(),
        at_pos <= l,
    ensures
        result.len() == l + p,
        forall|i: int| 0 <= i < p ==> #[trigger] result[at_pos + i] == nl[i],
        forall|i: int| 0 <= i < at_pos ==> #[trigger] result[i] == oline[i],
        forall|i: int| 0 <= i < (l - at_pos) ==> #[trigger] result[at_pos + p + i] == oline[at_pos + i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}