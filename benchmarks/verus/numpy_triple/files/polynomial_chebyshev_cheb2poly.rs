// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cheb2poly(c: Vec<i8>) -> (p: Vec<i8>)
    ensures

        p.len() == c.len(),

        (c.len() == 0 ==> p@ == c@),
        (c.len() == 1 ==> p@ == c@),
        (c.len() == 2 ==> p@ == c@),

        (c.len() == 4 ==>
            (c[0] == 0 && c[1] == 1 && c[2] == 2 && c[3] == 3) ==>
            (p[0] == -2 && p[1] == -8 && p[2] == 4 && p[3] == 12))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}