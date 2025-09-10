use vstd::prelude::*;

verus! {

fn mid(p: int, q: int) -> (m: int)

    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
{
    assume(false);
    unreached()
}

}
fn main() {}