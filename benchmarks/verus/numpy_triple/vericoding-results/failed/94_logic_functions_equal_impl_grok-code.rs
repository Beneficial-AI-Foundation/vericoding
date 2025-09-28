// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            result.len() == i as int,
            i as int <= x1.len()
        decreases x1.len() - i
    {
        result.push(x1[i] == x2[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}