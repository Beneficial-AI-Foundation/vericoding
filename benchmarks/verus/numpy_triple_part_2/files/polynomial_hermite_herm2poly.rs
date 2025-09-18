// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn herm2poly(c: Vec<i32>) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        /* Sanity checks */
        c.len() == 1 ==> result == c,
        c.len() == 2 ==> result[0] == c[0] && result[1] == 2 * c[1],
        /* Example from documentation: herm2poly([1, 2.75, 0.5, 0.375]) approximated with integers */
        (c.len() == 4 && c[0] == 1 && c[1] == 3 && c[2] == 1 && c[3] == 0) ==>
            (result[0] == 0 && result[1] == 1 && result[2] == 2 && result[3] == 3)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}