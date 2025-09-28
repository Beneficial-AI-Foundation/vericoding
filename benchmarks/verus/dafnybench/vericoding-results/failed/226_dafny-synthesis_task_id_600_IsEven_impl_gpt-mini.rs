use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
    let result: bool = n % 2 == 0;
    proof {
        assert(result <==> n % 2 == 0);
    }
    result
}
// </vc-code>

fn main() {
}

}