// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sqrt_helper(x: i8) -> (result: i8)
{
    if x == 0 { 0 }
    else if x == 1 { 1 }
    else if x == 4 { 2 }
    else if x == 9 { 3 }
    else if x == 16 { 4 }
    else if x == 25 { 5 }
    else if x == 36 { 6 }
    else if x == 49 { 7 }
    else if x == 64 { 8 }
    else if x == 81 { 9 }
    else if x == 100 { 10 }
    else if x == 121 { 11 }
    else { 0 }
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
    /* code modified by LLM (iteration 2): added type annotation for result */
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
            }
        decreases x.len() - i
    {
        let input = x[i];
        let s = sqrt_helper(input);
        result.push(s);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}