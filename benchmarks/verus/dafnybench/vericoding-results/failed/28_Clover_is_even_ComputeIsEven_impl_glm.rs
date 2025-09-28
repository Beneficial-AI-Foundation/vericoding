use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (is_even: bool)
    ensures (x % 2 == 0) == is_even
// </vc-spec>
// <vc-code>
{
    proof {
        assert(2 > 0);
    }
    (x % 2) == 0
}
// </vc-code>

fn main() {
}

}