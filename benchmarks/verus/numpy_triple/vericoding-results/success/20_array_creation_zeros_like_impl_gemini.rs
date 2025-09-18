// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn zeros_like(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0,
        forall|v: &Vec<i32>| v.len() == result.len() ==> {
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] + v[i] == v[i] && v[i] + result[i] == v[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            (i as int) <= a.len(),
            result.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == 0,
        decreases a.len() - i
    {
        result.push(0i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}