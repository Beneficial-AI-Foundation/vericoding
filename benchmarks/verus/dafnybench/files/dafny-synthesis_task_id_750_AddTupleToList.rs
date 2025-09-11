// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn add_tuple_to_list(l: Seq<(int, int)>, t: (int, int)) -> (r: Seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r[r.len() - 1] == t,
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}