// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch in vec_at_or_zero function */
fn vec_at_or_zero(vec: &Vec<i32>, index: usize) -> (value: i32)
    ensures value == if (index as int) < vec.len() { vec@[index as int] } else { 0 }
{
    if index < vec.len() {
        vec[index]
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type casting in loop invariant */
{
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < max_len
        invariant
            i <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if j < c1.len() as int { c1@[j] } else { 0 };
                let coeff2 = if j < c2.len() as int { c2@[j] } else { 0 };
                #[trigger] result@[j] == coeff1 + coeff2
            }
        decreases max_len - i
    {
        let coeff1 = vec_at_or_zero(&c1, i);
        let coeff2 = vec_at_or_zero(&c2, i);
        result.push(coeff1 + coeff2);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}