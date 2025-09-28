// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn chebder_helper(c: &Vec<i8>, scl: i8, j: int) -> (result: i8)
    requires
        0 <= j < c.len() as int - 1,
    ensures
        result == scl * (if j == 0 { c@[1] } else if j == 1 { 4 * c@[2] } else { 2 * ((j + 1) as i8) * c@[j + 1] }),
{
    /* helper modified by LLM (iteration 5): Remove ghost variable and fix type conversion */
    if j == 0 {
        scl * c@[1]
    } else if j == 1 {
        scl * 4 * c@[2]
    } else {
        scl * (2 * ((j + 1) as i8)) * c@[j + 1]
    }
}

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j as int] == scl * (2 * ((j + 1) as i8)) * c[(j + 1) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Remove ghost variable conversion, call helper directly with usize as int */
    let mut result = Vec::<i8>::new();
    
    let mut j: usize = 0;
    while j < c.len() - 1
        invariant
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] == chebder_helper(&c, scl, k),
            j <= c.len() - 1,
    {
        let val = chebder_helper(&c, scl, j as int);
        result.push(val);
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}