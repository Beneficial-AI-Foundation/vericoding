use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is in the implementation syntax
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mid(p: int, q: int) -> (m: int)
    // | ... | ??? | ... |
    //        p m   q
    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn mid(p: int, q: int) -> (m: int)
    requires
        p <= q,
    ensures
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
{
    let m: int = (p + q) / 2;
    m
}
// </vc-code>

fn main() {
}

}