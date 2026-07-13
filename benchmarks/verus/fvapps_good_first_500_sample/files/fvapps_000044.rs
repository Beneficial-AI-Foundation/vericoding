// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: nat, b: nat) -> nat;

spec fn will_indulge(a: nat, b: nat) -> bool {
    a != b && (gcd(a, b) == 1 || a % b == 0 || b % a == 0)
}

fn solve_seats(n: nat) -> (result: Vec<nat>)
    requires n > 0 && n <= 100,
    ensures
        result.len() == n,
        forall|x: nat| #[trigger] result@.contains(x) ==> x > 0 && x % 2 == 0,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] >= result[j],
        forall|i: int, j: int| 0 <= i < j < result.len() ==> !will_indulge(result[i], result[j]),
        forall|x: nat| #[trigger] result@.contains(x) ==> x > 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #eval sorted solve_seats(2)
    // #eval sorted solve_seats(3)  
    // #eval sorted solve_seats(4)
}