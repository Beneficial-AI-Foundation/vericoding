use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

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
// <vc-code>
{
    let m = p + (q - p) / 2;
    m
}
// </vc-code>

fn main() {
}

}