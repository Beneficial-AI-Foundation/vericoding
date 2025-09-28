// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn sign_element(val: i8) -> (sign: i8)
    ensures
        (val < 0 ==> sign == -1),
        (val == 0 ==> sign == 0),
        (val > 0 ==> sign == 1),
{
    if val < 0 {
        -1
    } else if val > 0 {
        1
    } else {
        0
    }
}

// </vc-helpers>

// <vc-spec>
fn sign(x: Vec<i8>) -> (result: Vec<i8>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            (x@[i] < 0 ==> result@[i] == -1) &&
            (x@[i] == 0 ==> result@[i] == 0) &&
            (x@[i] > 0 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed indexing syntax and verification */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (x@[j] < 0 ==> result@[j] == -1) &&
                (x@[j] == 0 ==> result@[j] == 0) &&
                (x@[j] > 0 ==> result@[j] == 1)
            }
        decreases x@.len() - i
    {
        let element = x[i];
        let signed = sign_element(element);
        result.push(signed);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}