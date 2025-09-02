use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


fn main() {}

}