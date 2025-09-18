// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use proper type conversion with usize parameter */
fn equal_helper(x1: Vec<String>, x2: Vec<String>, i: usize) -> (result: bool)
    requires 0 <= i < x1.len() && x1.len() == x2.len()
    ensures result == (x1[i] == x2[i])
{
    x1[i] == x2[i]
}
// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> x1[i] == x2[i]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix helper call with usize parameter instead of int */
{
    let mut result = Vec::new();
    let n: usize = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as usize] == (x1[j as usize] == x2[j as usize])
    {
        let elem = equal_helper(x1, x2, i);
        result.push(elem);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}