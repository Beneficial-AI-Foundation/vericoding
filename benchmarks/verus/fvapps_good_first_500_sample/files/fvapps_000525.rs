// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_moves_to_exit(n: nat) -> (result: nat)
    requires n > 0,
    ensures 
        result > 0,
        result <= 4 * n,
        (n % 2 == 0) ==> (result == n * 4),
        (n % 4 == 3) ==> (result == n),
        (n % 2 != 0 && n % 4 != 3) ==> (result == n * 2),
        n == 1 ==> result == 2,
        n == 2 ==> result == 8,
        n == 3 ==> result == 3,
        n == 4 ==> result == 16,
        n == 7 ==> result == 7,
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
    // Assurance level: guarded_and_plausible
}