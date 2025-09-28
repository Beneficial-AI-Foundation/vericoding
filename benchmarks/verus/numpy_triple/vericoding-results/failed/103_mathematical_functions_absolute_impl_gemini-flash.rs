// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Added decreases clause to the while loop. */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            0 <= i as int && i as int <= x.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] as int == abs_spec(x@[j] as int),
            forall|j: int| 0 <= j < i as int ==> result@[j] as int >= 0,
            forall|j: int| 0 <= j < i as int ==> (result@[j] as int == 0 <==> x@[j] as int == 0),
        decreases x.len() - i
    {
        let val = x[i];
        let abs_val: i8;
        if val >= 0 {
            abs_val = val;
        } else {
            abs_val = -val;
        }
        result.push(abs_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}