use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// <vc-code>
{
    let x_int = x as int;
    let y_int = y as int;
    let quot = x_int / y_int;
    let rem = x_int % y_int;
    let result = (rem, quot);
    assert(0 <= rem < y_int);
    assert(quot * y_int + rem == x_int);
    assert(0 <= quot);
    result
}
// </vc-code>

fn main() {
}

}