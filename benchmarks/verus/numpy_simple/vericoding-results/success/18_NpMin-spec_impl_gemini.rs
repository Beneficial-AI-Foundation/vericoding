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
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i]
// </vc-spec>
// <vc-code>
{
    let mut m: i8 = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            exists|j: int| 0 <= j < i && m as int == a@[j],
            forall|j: int| 0 <= j < i ==> m as int <= a@[j],
        decreases a.len() - i
    {
        if a[i] < m {
            m = a[i];
        }
        i = i + 1;
    }
    m
}
// </vc-code>


}
fn main() {}