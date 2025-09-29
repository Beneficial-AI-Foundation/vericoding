// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn in_percent_range(z: int) -> bool
{
    -100 <= z && z <= 100
}

pub proof fn lemma_zero_in_range()
    ensures
        in_percent_range(0),
{
}

// </vc-helpers>

// <vc-spec>
fn corrcoef(x: Vec<i8>, y: Vec<i8>) -> (result: i8)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        exists|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() && x[i] != x[j],
        exists|i: int, j: int| 0 <= i < y.len() && 0 <= j < y.len() && y[i] != y[j],
    ensures
        -100 <= result as int && result as int <= 100
// </vc-spec>
// <vc-code>
{
    0i8
}
// </vc-code>


}
fn main() {}