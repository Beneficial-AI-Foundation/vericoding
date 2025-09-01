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
    let mut r: i32 = 0;
    while (r + 1) * (r + 1) <= n
        invariant 0 <= r && r * r <= n && r <= n
        decreases n - r
    {
        r = r + 1;
    }
    proof {
        // Use spec ints for reasoning about squares and non-overflow
        let r_int: int = r as int;
        let n_int: int = n as int;
        assert(0 <= r_int);
        assert(r_int * r_int <= n_int);
        assert(!((r_int + 1) * (r_int + 1) <= n_int));
        // Relate back to i32-level postconditions
        assert((r as int) * (r as int) <= n as int);
        assert(n as int < ((r as int) + 1) * ((r as int) + 1));
    }
    r
}
// </vc-code>

fn main() {}
}