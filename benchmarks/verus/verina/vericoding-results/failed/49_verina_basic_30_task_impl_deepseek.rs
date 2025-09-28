// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parameter types to use i32 instead of int */
spec fn modulo(a: i32, b: i32) -> i32
    requires b != 0
{
    a % b
}
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch by using i32 values directly */
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < a.len()
        invariant
            result@.len() == index,
            forall|j: int| 0 <= j < index ==> result@[j] == modulo(a[j] as i32, b[j] as i32),
        decreases a.len() - index
    {
        result.push(a[index] % b[index]);
        index += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}