use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (is_even: bool)
    ensures (x % 2 == 0) == is_even
// </vc-spec>
// <vc-code>
{
    proof {
        return (x % (2 as int)) == (0 as int);
    }
}
// </vc-code>

fn main() {
}

}