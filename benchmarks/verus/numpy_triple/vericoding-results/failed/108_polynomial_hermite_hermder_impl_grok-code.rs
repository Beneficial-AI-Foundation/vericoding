// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn first_derivative(coeffs: &Vec<i32>, scl: i32) -> Vec<i32>
{
    if coeffs.len() == 0 {
        return Vec::new();
    }
    let mut result = Vec::with_capacity(coeffs.len() - 1);
    for i in 0..(coeffs.len() - 1) {
        let factor = scl * (i as i32 + 1) * 2;
        result.push(factor * coeffs[i + 1]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
{
    if m >= c.len() {
        return Vec::new();
    }
    let mut current = c.clone();
    for _ in 0..m {
        current = first_derivative(&current, scl);
    }
    current
}
// </vc-code>

}
fn main() {}