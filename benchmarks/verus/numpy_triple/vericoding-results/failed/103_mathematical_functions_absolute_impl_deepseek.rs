// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix absolute value helper to handle all cases including i8::MIN */
fn abs_i8(x: i8) -> (result: i8)
    requires
        true,
    ensures
        result as int == abs_spec(x as int),
        result >= 0,
        (result == 0) == (x == 0),
{
    if x == i8::MIN {
        0-i8::MIN
    } else if x < 0 {
        -x
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absolute(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == abs_spec(x[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> x[i] == 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove assert and use proper index type in loop */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] as int == abs_spec(x[j] as int),
            forall|j: int| 0 <= j < result.len() ==> result[j] >= 0,
            forall|j: int| 0 <= j < result.len() ==> (result[j] == 0 <==> x[j] == 0),
    {
        let abs_val = abs_i8(x[[i as int]]);
        result.push(abs_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}