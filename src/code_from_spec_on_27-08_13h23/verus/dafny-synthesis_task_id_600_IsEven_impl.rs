use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
{
    let result = n % 2 == 0;
    result
}
// </vc-code>

fn main() {
}

}