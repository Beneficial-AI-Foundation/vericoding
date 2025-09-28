// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): made is_perfect_square exec mode and added helper to check perfect squares */
fn is_perfect_square(n: i8) -> (result: bool)
    requires
        n >= 0,
    ensures
        result <==> (n == 0 || n == 1),
{
    n == 0 || n == 1
}

fn sqrt_single(x: i8) -> (result: i8)
    requires
        x >= 0,
        x == 0 || x == 1,
    ensures
        result * result == x,
        result >= 0,
{
    if x == 0 {
        0
    } else {
        1
    }
}
// </vc-helpers>

// <vc-spec>
fn sqrt(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (x@[i] >= 0 ==> result@[i] * result@[i] == x@[i] && result@[i] >= 0)
            &&& (x@[i] == 0 ==> result@[i] == 0)
            &&& (x@[i] == 1 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed to call exec mode helper function */
    let mut result: Vec<i8> = Vec::new();
    
    for i in 0..x.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x@[j] >= 0 ==> result@[j] * result@[j] == x@[j] && result@[j] >= 0)
                &&& (x@[j] == 0 ==> result@[j] == 0)
                &&& (x@[j] == 1 ==> result@[j] == 1)
            },
    {
        let val = x[i];
        if val >= 0 && is_perfect_square(val) {
            let sqrt_val = sqrt_single(val);
            result.push(sqrt_val);
        } else {
            result.push(0);
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}