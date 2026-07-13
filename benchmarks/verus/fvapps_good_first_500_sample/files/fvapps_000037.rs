// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * fact((n - 1) as nat)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_good_permutations(n: usize, k: u64) -> (result: Vec<usize>)
    requires n <= 50, k >= 1,
    ensures
        (n == 0 && k == 1 ==> result.len() == 0) &&
        (n > 0 && result.len() > 1 ==> 
            result.len() == n &&
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j] &&
            forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= n) &&
        (n > 0 && k > fact((n - 1) as nat) * (n as nat) ==> result.len() == 1 && result[0] == 0)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn factorial(n: usize) -> (result: u64)
    ensures result == fact(n as nat)
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
}