use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    n % 2 == 0
}
// </vc-code>

fn main() {
}

}