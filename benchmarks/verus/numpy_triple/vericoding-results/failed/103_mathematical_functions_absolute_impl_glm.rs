// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed ghost type usage */
fn abs_i8(x: i8) -> (result: i8)
    ensures
        result >= 0,
        result as int == if x >= 0 { x as int } else { - (x as int) },
        (result == 0) == (x == 0)
{
    if x >= 0 {
        x
    } else {
        -x
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
/* code modified by LLM (iteration 2): implemented absolute value for vector */
{
    let mut result = Vec::new();
    let len = x.len();
    result.reserve(len);
    for i in 0..len {
        let elem = x[i];
        let abs_elem = abs_i8(elem);
        result.push(abs_elem);
    }
    result
}
// </vc-code>


}
fn main() {}