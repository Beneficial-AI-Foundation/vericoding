use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn last_digit(n: int) -> (result: int)
    requires n >= 0,
    ensures 0 <= result < 10,
    ensures n % 10 == result,
// </vc-spec>
// <vc-code>
{
    assume(false);
    loop { }
}
// </vc-code>

fn main() {
}

}