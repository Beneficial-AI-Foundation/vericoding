// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, a@.map(|i, x| x as int)),
    ensures 
        result >= 1,
        #[trigger] exists|i: int| is_optimal_choice(k as int, a@.map(|i, x| x as int), i) && result as int == hours_needed(k as int, a@.map(|i, x| x as int)[i]),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}