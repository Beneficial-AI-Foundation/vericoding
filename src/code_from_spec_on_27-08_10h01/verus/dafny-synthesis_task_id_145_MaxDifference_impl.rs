use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max_in_slice(a: &[i32]) -> i32
    recommends a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let rest_max = max_in_slice(&a[1..]);
        if a[0] > rest_max { a[0] } else { rest_max }
    }
}

spec fn min_in_slice(a: &[i32]) -> i32
    recommends a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let rest_min = min_in_slice(&a[1..]);
        if a[0] < rest_min { a[0] } else { rest_min }
    }
}

proof fn max_in_slice_correct(a: &[i32])
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= max_in_slice(a)
    ensures exists|i: int| 0 <= i < a.len() && a[i] == max_in_slice(a)
    decreases a.len()
{
    if a.len() == 1 {
    } else {
        max_in_slice_correct(&a[1..]);
    }
}

proof fn min_in_slice_correct(a: &[i32])
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> min_in_slice(a) <= a[i]
    ensures exists|i: int| 0 <= i < a.len() && a[i] == min_in_slice(a)
    decreases a.len()
{
    if a.len() == 1 {
    } else {
        min_in_slice_correct(&a[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// </vc-spec>

// <vc-code>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
{
    proof {
        max_in_slice_correct(a);
        min_in_slice_correct(a);
    }
    max_in_slice(a) - min_in_slice(a)
}
// </vc-code>

fn main() {
}

}