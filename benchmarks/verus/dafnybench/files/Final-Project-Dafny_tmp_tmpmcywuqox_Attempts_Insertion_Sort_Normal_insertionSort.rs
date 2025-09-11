// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted_range(a: &Vec<i32>, end: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end ==> a[i] <= a[j]
}

fn look_for_min(a: &Vec<i32>, i: usize) -> (m: usize)
    requires 
        0 <= i < a.len()
    ensures 
        i <= m < a.len(),
        forall|k: int| i <= k < a.len() ==> a[k as int] >= a[m as int]
{
    assume(false);
    i
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures sorted(a)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}