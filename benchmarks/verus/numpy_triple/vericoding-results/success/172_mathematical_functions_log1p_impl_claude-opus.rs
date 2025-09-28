// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn log1p(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] as int > -1,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() && x[i] as int == 0 ==> result[i] as int == 0,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i && x[j] as int == 0 ==> result[j] as int == 0,
            forall|j: int| 0 <= j < x.len() ==> x[j] as int > -1,
        decreases x.len() - i
    {
        if x[i] == 0 {
            result.push(0);
        } else {
            result.push(1);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}