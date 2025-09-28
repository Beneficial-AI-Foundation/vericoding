use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed; the implementation is corrected directly in the code section
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
    n % 2i == 0i
}
// </vc-code>

fn main() {
}

}