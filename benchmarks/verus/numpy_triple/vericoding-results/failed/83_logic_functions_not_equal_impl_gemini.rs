// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_not_equal<T: PartialEq>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i]),

        (x1@ == x2@) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false),

        forall|i: int| 0 <= i < result.len() ==> result[i] == (x2[i] != x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed incorrect assert statement */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] != x2@[j]),
        decreases x1.len() - i
    {
        let ne = x1[i] != x2[i];
        result.push(ne);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}