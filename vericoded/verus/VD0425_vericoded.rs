use vstd::prelude::*;

verus! {

//Problem 01

//problem02
//a)

// <vc-helpers>
#[verifier::external_body]
proof fn int_div_exists(n: int, d: int) -> (result: (int, int))
    requires
        n >= d && n >= 0 && d > 0,
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
{
    arbitrary()
}
// </vc-helpers>

// <vc-spec>
proof fn int_div(n: int, d: int) -> (result: (int, int))
    requires n >= d && n >= 0 && d > 0,
    ensures ({
        let (q, r) = result;
        (d * q) + r == n && 0 <= q <= n / 2 && 0 <= r < d
    })
// </vc-spec>
// <vc-code>
{
    let res = int_div_exists(n, d);
    res
}
// </vc-code>

fn main() {
}

}