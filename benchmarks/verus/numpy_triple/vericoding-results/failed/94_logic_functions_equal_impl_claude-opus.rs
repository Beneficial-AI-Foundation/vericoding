// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): adding exec_equality function for runtime comparison */
fn exec_equality<T>(a: &T, b: &T) -> (result: bool)
    ensures
        result == (a == b)
{
    *a == *b
}
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
    /* code modified by LLM (iteration 5): fixing exec_equality call syntax */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] == x2@[j]),
    {
        let eq: bool = exec_equality(&x1[i], &x2[i]);
        result.push(eq);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}