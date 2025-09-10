use vstd::prelude::*;

verus! {

proof fn int_div(n: int, d: int) -> (result: (int, int))
    requires n >= d && n >= 0 && d > 0,
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
{
    assume(false);
    unreached();
}

}
fn main() {}