// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeweight(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = if x[i] % 2 == 0 { x[i] + 1 } else { x[i] - 1 };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}