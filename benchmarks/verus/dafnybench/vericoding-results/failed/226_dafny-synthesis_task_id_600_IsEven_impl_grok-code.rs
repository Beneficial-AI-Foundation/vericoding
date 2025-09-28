use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
n % 2int == 0int
}
// </vc-code>

fn main() {
}

}