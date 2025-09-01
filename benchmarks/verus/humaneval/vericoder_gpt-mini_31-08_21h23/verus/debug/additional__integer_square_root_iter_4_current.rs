use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut r: int = 0;
    let n_int: int = n as int;
    while (r + 1) * (r + 1) <= n_int
        invariant 0 <= r && r * r <= n_int && r <= n_int
        decreases n_int - r
    {
        r = r + 1;
    }
    proof {
        // From the invariant we have r*r <= n_int and r >= 0
        assert(r * r <= n_int);
        assert(0 <= r);
        // Loop exit condition
        assert(!((r + 1) * (r + 1) <= n_int));
        // Convert to i32 and back to int to relate to the specification's types
        let res_i32: i32 = r as i32;
        let res_int: int = res_i32 as int;
        // res_int equals r because r is between 0 and n_int and n_int originates from an i32
        assert(res_int * res_int <= n_int);
        assert(n_int < (res_int + 1) * (res_int + 1));
    }
    r as i32
}
// </vc-code>

fn main() {}
}