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
    let mut idx: usize = 1;
    let mut min_val: i8 = a[0];
    while idx < a.len()
        invariant
            1 <= idx <= a@.len(),
            exists |j: int| 0 <= j < idx && a@[j] == min_val as int,
            forall |j: int| 0 <= j < idx ==> min_val as int <= a@[j],
        decreases a@.len() - idx,
    {
        if a[idx] < min_val {
            min_val = a[idx];
        }
        idx = idx + 1;
    }
    min_val
}
// </vc-code>


}
fn main() {}