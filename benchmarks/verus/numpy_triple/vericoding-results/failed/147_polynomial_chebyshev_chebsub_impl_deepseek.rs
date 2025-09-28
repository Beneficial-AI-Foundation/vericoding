// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): fixed type conversions to use usize instead of int */
proof fn vec_sub_proof(c1: &Vec<i8>, c2: &Vec<i8>, result: &Vec<i8>, i: usize)
    requires
        c1.len() == c2.len(),
        result.len() == c1.len(),
        0 <= i <= c1.len(),
        forall|j: int| 0 <= j < i ==> result@[j] == (((c1@[j] as int) - (c2@[j] as int)) as i8),
    ensures
        forall|j: int| 0 <= j < c1.len() ==> result@[j] == (((c1@[j] as int) - (c2@[j] as int)) as i8),
    decreases c1.len() - i,
{
    if i < c1.len() {
        vec_sub_proof(c1, c2, result, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn chebsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversions to use usize instead of int */
    let mut result = Vec::new();
    let n = c1.len();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (((c1@[j] as int) - (c2@[j] as int)) as i8),
    {
        result.push((((c1[i] as i32) - (c2[i] as i32)) as i8));
        i += 1;
    }
    proof {
        vec_sub_proof(&c1, &c2, &result, 0);
    }
    result
}
// </vc-code>


}
fn main() {}