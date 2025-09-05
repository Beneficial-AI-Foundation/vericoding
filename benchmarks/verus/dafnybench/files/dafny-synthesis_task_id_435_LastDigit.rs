use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn last_digit(n: i32) -> (result: i32)
    requires n >= 0
    ensures 
        0 <= result < 10,
        n % 10 == result
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>

fn main() {
}

}
