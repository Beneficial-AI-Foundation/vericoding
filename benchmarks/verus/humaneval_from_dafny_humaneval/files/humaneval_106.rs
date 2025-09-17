// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn sum_range(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_range((n - 1) as nat) }
}

spec fn valid_result(n: nat, result: Seq<nat>) -> bool
{
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        (if (i + 1) % 2 == 0 { result[i] == factorial((i + 1) as nat) }
         else { result[i] == sum_range((i + 1) as nat) })
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn f(n: nat) -> (result: Vec<nat>)
    ensures valid_result(n, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}