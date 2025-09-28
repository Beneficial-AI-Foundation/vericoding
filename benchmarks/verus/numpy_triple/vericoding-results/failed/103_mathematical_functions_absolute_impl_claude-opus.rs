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
    /* code modified by LLM (iteration 4): fixed loop invariant and overflow handling */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == abs_spec(x[j] as int),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < i ==> (result[j] == 0 <==> x[j] == 0),
        decreases x.len() - i
    {
        let val = x[i];
        let abs_val = if val >= 0 { 
            val 
        } else if val == i8::MIN {
            i8::MAX
        } else { 
            -val 
        };
        result.push(abs_val);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}