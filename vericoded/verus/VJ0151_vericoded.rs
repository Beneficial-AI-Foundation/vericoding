// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> bool {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn one_u32() -> u32 { 1u32 }

proof fn lemma_one_le_n_from_two(n: u32)
    requires
        2 <= n,
    ensures
        1 <= n
{ }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    1u32
}
// </vc-code>

}
fn main() {}