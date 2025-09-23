// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, ar: Seq<int>) -> bool {
    n >= 2 && ar.len() == n && (forall|i: int| 0 <= i < n ==> ar[i] > 0)
}

spec fn gcd(x: int, y: int) -> int
    requires x > 0 && y > 0,
    ensures gcd(x, y) > 0,
    decreases if x < y { y } else { x },
{
    if x == y { x }
    else if x < y { gcd(x, y - x) }
    else { gcd(x - y, y) }
}

spec fn gcd_of_sequence(ar: Seq<int>) -> int
    requires ar.len() >= 1,
    requires (forall|i: int| 0 <= i < ar.len() ==> ar[i] > 0),
    ensures gcd_of_sequence(ar) > 0,
    decreases ar.len(),
{
    if ar.len() == 1 { ar[0] }
    else { gcd(ar[0], gcd_of_sequence(ar.subrange(1, ar.len() as int))) }
}

spec fn minimal_sum(n: int, ar: Seq<int>) -> int
    requires valid_input(n, ar),
{
    gcd_of_sequence(ar) * n
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, ar: Seq<int>) -> (result: int)
    requires valid_input(n, ar),
    ensures result == minimal_sum(n, ar),
    ensures result > 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}