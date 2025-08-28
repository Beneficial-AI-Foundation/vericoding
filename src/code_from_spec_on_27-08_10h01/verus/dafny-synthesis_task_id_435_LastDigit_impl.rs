use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn last_digit(n: int) -> (result: int)
    requires n >= 0,
    ensures 0 <= result < 10,
    ensures n % 10 == result,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn last_digit(n: int) -> (result: int)
    requires n >= 0,
    ensures 0 <= result < 10,
    ensures n % 10 == result,
{
    n % 10
}
// </vc-code>

fn main() {
}

}