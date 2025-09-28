// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, helper is correct */
spec fn get_rotated_index(i: int, n: int, len: nat) -> int
    requires len > 0
{
    (i - n + (len as int)) % (len as int)
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by comparing l.len() with 0nat */
    if l.len() > 0nat {
        Seq::new(l.len(), |i: int| l.index(get_rotated_index(i, n, l.len())))
    } else {
        Seq::empty()
    }
}
// </vc-code>

}
fn main() {}