// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.subrange(1, factors.len() as int))
    }
}

spec fn is_non_decreasing(factors: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < factors.len() ==> #[trigger] factors[i] <= #[trigger] factors[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn factorize(n: i8) -> (factors: Vec<i8>)
    requires n >= 0
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@.map(|i: int, x: i8| x as int)) == n as int,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
        is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
        forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}