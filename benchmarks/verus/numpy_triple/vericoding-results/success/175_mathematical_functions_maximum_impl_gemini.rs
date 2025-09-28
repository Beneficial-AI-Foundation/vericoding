// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i8(a: i8, b: i8) -> (result: i8)
    ensures
        result == if a >= b { a } else { b },
        result >= a && result >= b,
        result == a || result == b,
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn maximum(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == if x1@[i] >= x2@[i] { x1@[i] } else { x2@[i] },
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] >= x1@[i] && result@[i] >= x2@[i],
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == x1@[i] || result@[i] == x2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added type annotation to fix compilation error */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j] == if x1@[j] >= x2@[j] { x1@[j] } else { x2@[j] },
            forall|j: int| 0 <= j < i ==> 
                result@[j] >= x1@[j] && result@[j] >= x2@[j],
            forall|j: int| 0 <= j < i ==> 
                result@[j] == x1@[j] || result@[j] == x2@[j],
        decreases x1.len() - i
    {
        let e1 = x1[i];
        let e2 = x2[i];
        let m = max_i8(e1, e2);
        result.push(m);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}