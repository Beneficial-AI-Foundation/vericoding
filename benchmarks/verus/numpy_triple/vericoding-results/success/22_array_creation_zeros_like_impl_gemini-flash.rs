// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */

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
/* code modified by LLM (iteration 2): added decreases clause to while loop */
{
    let mut result = Vec::new();
    let len = a.len();
    let mut i = 0;

    while i < len
        invariant
            result.len() == i,
            len == a.len(),
            forall|j: int| 0 <= j < i ==> result.len() == i && result@[j] == 0,
            i <= len
        decreases len - i
    {
        result.push(0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}