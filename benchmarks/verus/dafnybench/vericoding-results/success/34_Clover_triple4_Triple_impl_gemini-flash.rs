use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn triple(x: int) -> (r: int)
    ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
    let mut result: int = 0;
    //@ ghost
    //@ assert((3 * x) == (x + x + x));

    result = x + x;
    result = result + x;

    assert(result == 3 * x);
    result
}
// </vc-code>

fn main() {
}

}