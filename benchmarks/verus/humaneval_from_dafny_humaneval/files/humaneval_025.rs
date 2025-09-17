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
proof fn product_append(factors: Seq<int>, x: int)
    ensures product(factors.add(seq![x])) == product(factors) * x
    decreases factors.len()
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: int) -> (factors: Vec<int>)
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@) == n,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i]),
        is_non_decreasing(factors@),
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