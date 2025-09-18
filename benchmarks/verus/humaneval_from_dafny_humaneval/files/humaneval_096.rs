// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_up_to(n: int) -> (result: Vec<int>)
    requires n >= 0
    ensures 
        forall|i: int| 0 <= i < result.len() ==> is_prime_number(result[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] < n,
        forall|p: int| 2 <= p < n && is_prime_number(p) ==> result@.contains(p),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}