// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        exists|i: int| 0 <= i < a@.len() && a@[i] == result as int,
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i],
// </vc-spec>
// <vc-code>
{
    let mut min_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < i && a@[k] == min_val as int,
            forall|k: int| 0 <= k < i ==> min_val as int <= a@[k],
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-code>


}
fn main() {}