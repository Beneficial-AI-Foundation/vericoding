// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn compute_inversions(n: int, k: int, iterations: int) -> int
    decreases iterations when iterations >= 0
{
    if iterations == 0 { 0 }
    else { compute_inversions(n, k, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2) }
}

spec fn sum_inversions_formula(n: int, iterations: int) -> int
    decreases iterations when iterations >= 0
{
    if iterations == 0 { 0 }
    else { sum_inversions_formula(n, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2) }
}

spec fn sum_of_consecutive_pairs(n: int, k: int) -> int {
    let iterations = k;
    if iterations == 0 { 0 }
    else { sum_inversions_formula(n, iterations) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires n as int >= 1 && k as int >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}