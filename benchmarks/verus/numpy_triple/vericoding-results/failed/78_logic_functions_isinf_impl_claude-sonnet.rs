// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax by removing uninterp keyword and using body with unimplemented! for spec function */
exec fn check_infinity(x: f64) -> (result: bool)
    ensures result == is_infinite(x)
{
    x.is_infinite()
}
// </vc-helpers>

// <vc-spec>
fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x[i])
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use direct f64::is_infinite() method call */
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_infinite(x[j])
    {
        let is_inf = check_infinity(x[i]);
        result.push(is_inf);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}