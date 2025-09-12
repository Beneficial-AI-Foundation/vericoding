// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    n >= 1 && k >= 1 && a.len() == n &&
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 1) &&
    (exists|i: int| 0 <= i < a.len() && k % a[i] == 0)
}

spec fn valid_bucket(k: int, bucket_size: int) -> bool {
    bucket_size >= 1 && k % bucket_size == 0
}

spec fn hours_needed(k: int, bucket_size: int) -> int
    recommends valid_bucket(k, bucket_size)
{
    k / bucket_size
}

spec fn is_optimal_choice(k: int, a: Seq<int>, chosen_bucket: int) -> bool {
    0 <= chosen_bucket < a.len() &&
    valid_bucket(k, a[chosen_bucket]) &&
    (forall|i: int| 0 <= i < a.len() && valid_bucket(k, a[i]) ==> a[i] <= a[chosen_bucket])
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, a: Seq<int>) -> (result: int)
    requires valid_input(n, k, a)
    ensures result >= 1
    ensures exists|i: int| is_optimal_choice(k, a, i) && result == hours_needed(k, a[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}