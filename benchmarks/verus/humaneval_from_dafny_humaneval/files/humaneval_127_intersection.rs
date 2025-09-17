// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| #[trigger] (n % k) != 0 ==> 2 <= k < n
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn intersection(start1: int, end1: int, start2: int, end2: int) -> (result: String)
    requires start1 <= end1 && start2 <= end2,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1, start2) <= min(end1, end2) && is_prime((min(end1, end2) - max(start1, start2) + 1) as nat))),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}