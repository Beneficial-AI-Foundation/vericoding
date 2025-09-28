// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= result as int
// </vc-spec>
// <vc-code>
{
    let mut result = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|j: int| 0 <= j < a@.len() && result as int == a@[j],
            forall|j: int| 0 <= j < i ==> a@[j] <= result as int
        decreases a.len() - i
    {
        if a[i] > result {
            result = a[i];
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}