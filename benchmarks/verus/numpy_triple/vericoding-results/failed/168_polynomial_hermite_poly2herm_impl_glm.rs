// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn poly2herm_helper(pol: &Vec<f64>, i: int) -> f64
    requires
        0 <= i < pol@.len(),
    ensures
        poly2herm_helper(pol, i) == pol@[i],
{
    pol@[i]
}
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
    let mut result = Vec::new();
    let n = pol.len();
    
    if n == 0 {
        return result;
    }
    
    result.push(poly2herm_helper(&pol, 0));
    
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == poly2herm_helper(&pol, j),
        decreases n - i
    {
        result.push(poly2herm_helper(&pol, i));
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}