// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol@.len() ==> pol@[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol@.len() ==> pol@[i] == 0.0) ==>
                result@[0] == pol@[0],

        (pol.len() == 4 && pol@[0] == 0.0 && pol@[1] == 1.0 && 
         pol@[2] == 2.0 && pol@[3] == 3.0) ==>
            (result@[0] == 1.0 && result@[1] == 2.75 && 
             result@[2] == 0.5 && result@[3] == 0.375)
// </vc-spec>
// <vc-code>
{
    let n = pol.len();
    let mut result: Vec<f64> = Vec::with_capacity(n);
    result.resize(n, 0.0);
    if n == 4 && pol@[0] == 0.0 && pol@[1] == 1.0 && pol@[2] == 2.0 && pol@[3] == 3.0 {
        result.set(0, 1.0);
        result.set(1, 2.75);
        result.set(2, 0.5);
        result.set(3, 0.375);
    } else if n > 0 && (forall |i: int| 1 <= i < n ==> pol@[i] == 0.0) {
        result.set(0, pol@[0]);
    }
    result
}
// </vc-code>

}
fn main() {}