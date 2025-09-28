// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_greater(x1: &Vec<i8>, x2: &Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == (x1[i] as int > x2[i] as int)) &&
            (result[i] == true ==> !(x2[i] as int > x1[i] as int)) &&
            (result[i] == true || result[i] == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] as int > x2[j] as int),
            forall|j: int| 0 <= j < i ==> (result[j] == true ==> !(x2[j] as int > x1[j] as int)),
            forall|j: int| 0 <= j < i ==> (result[j] == true || result[j] == false),
        decreases x1.len() - i
    {
        let cmp = x1[i] > x2[i];
        result.push(cmp);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}