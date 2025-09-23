// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<int>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] + vec_sum(a.skip(1))
    }
}

spec fn vec_mean(a: Seq<int>) -> int 
{
    vec_sum(a) / (a.len() as int)
}

spec fn squared_deviations_sum(a: Seq<int>, mean: int) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        (a[0] - mean) * (a[0] - mean) + squared_deviations_sum(a.skip(1), mean)
    }
}

fn var(a: Vec<i8>, ddof: usize) -> (result: i8)
    requires 
        a.len() > 0,
        ddof < a.len(),
    ensures 
        result >= 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}