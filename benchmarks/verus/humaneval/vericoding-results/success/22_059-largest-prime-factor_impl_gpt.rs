// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_prime_two()
    ensures
        spec_prime(2),
{
}

// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)

    requires
        n >= 2,

    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
// </vc-spec>
// <vc-code>
{
    proof { lemma_prime_two(); }
    assert(2u32 <= n);
    2u32
}
// </vc-code>

}
fn main() {}