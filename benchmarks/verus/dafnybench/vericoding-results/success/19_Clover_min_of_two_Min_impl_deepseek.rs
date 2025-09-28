use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn min_ensures(x: int, y: int, z: int)
    requires
        z == (if x <= y { x } else { y })
    ensures
        (x <= y ==> z == x) && (x > y ==> z == y)
{
    if x <= y {
        assert(z == x);
    } else {
        assert(z == y);
    }
}
// </vc-helpers>

// <vc-spec>
fn min(x: int, y: int) -> (z: int)
    ensures
        x <= y ==> z == x,
        x > y ==> z == y,
// </vc-spec>
// <vc-code>
{
    let z = if x <= y {
        let result = x;
        proof { min_ensures(x, y, result); }
        result
    } else {
        let result = y;
        proof { min_ensures(x, y, result); }
        result
    };
    z
}
// </vc-code>

fn main() {}

}