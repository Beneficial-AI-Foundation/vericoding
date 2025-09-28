// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_i32(a: i32, b: i32) -> (result: i32)
    ensures
        (result == a || result == b),
        result <= a,
        result <= b,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
{
    let mut min = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> min <= a[j],
            exists|k: int| 0 <= k < i && min == a[k],
        decreases a.len() - i,
    {
        min = min_i32(min, a[i]);
        i = i + 1;
    }
    min
}
// </vc-code>

}
fn main() {}