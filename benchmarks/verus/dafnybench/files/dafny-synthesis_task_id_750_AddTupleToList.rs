// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn add_tuple_to_list(l: Vec<(i8, i8)>, t: (i8, i8)) -> (r: Vec<(i8, i8)>)
    ensures
        r@.len() == l@.len() + 1,
        r@[r@.len() - 1] == t,
        forall|i: int| 0 <= i < l@.len() ==> r@[i] == l@[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}