// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x@[j] >= 0 ==> result@[j] * result@[j] == x@[j] && result@[j] >= 0)
                &&& (x@[j] == 0 ==> result@[j] == 0)
                &&& (x@[j] == 1 ==> result@[j] == 1)
            },
        decreases x.len() - i
    {
        let val = x[i];
        if val == 0 {
            result.push(0);
        } else if val == 1 {
            result.push(1);
        } else if val == 4 {
            result.push(2);
        } else if val == 9 {
            result.push(3);
        } else if val == 16 {
            result.push(4);
        } else if val == 25 {
            result.push(5);
        } else if val == 36 {
            result.push(6);
        } else if val == 49 {
            result.push(7);
        } else if val == 64 {
            result.push(8);
        } else if val == 81 {
            result.push(9);
        } else if val == 100 {
            result.push(10);
        } else if val == 121 {
            result.push(11);
        } else {
            result.push(0);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}