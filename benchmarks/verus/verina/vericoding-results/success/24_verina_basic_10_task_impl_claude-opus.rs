// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    let mut j = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            forall|i: int| 0 <= i < j ==> n > a[i],
        decreases a.len() - j,
    {
        if n <= a[j] {
            return false;
        }
        j = j + 1;
    }
    true
}
// </vc-code>

}
fn main() {}