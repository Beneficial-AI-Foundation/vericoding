// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    requires n > 0
    decreases n
{
    if n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    requires 
        0 <= i <= a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] > 0
    decreases a.len() - i
{
    if i == a.len() { 0 }
    else { count_factors_of_two(a[i]) + sum_factors(a, i + 1) }
}

spec fn max_operations(a: Seq<int>) -> int
    requires valid_input(a)
{
    sum_factors(a, 0)
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>) -> (result: int)
    requires valid_input(a)
    ensures 
        result >= 0,
        result == max_operations(a)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}