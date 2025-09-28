// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_in_vec(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result >= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
{
    let mut max_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> max_val >= a[j],
            exists|j: int| 0 <= j < i && max_val == a[j],
        decreases a.len() - i,
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    let max_val = max_in_vec(a);
    n > max_val
}
// </vc-code>

}
fn main() {}