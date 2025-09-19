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
        forall|i: int| 0 <= i < p as int ==> #[trigger] result[at_pos as int + i] == nl[i],
        forall|i: int| 0 <= i < at_pos as int ==> #[trigger] result[i] == oline[i],
        forall|i: int| 0 <= i < (l as int - at_pos as int) ==> #[trigger] result[at_pos as int + p as int + i] == oline[at_pos as int + i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}