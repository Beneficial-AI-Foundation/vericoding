// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nextafter(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Identity case: when x1 equals x2, result equals x1 */
            (x1[i] == x2[i] ==> result[i] == x1[i]) &&
            /* Direction consistency: result moves towards x2 */
            ((x1[i] < x2[i] ==> x1[i] < result[i] && result[i] <= x2[i]) &&
             (x1[i] > x2[i] ==> x1[i] > result[i] && result[i] >= x2[i])) &&
            /* Finiteness preservation: if both inputs are finite and different, result is defined */
            (x1[i] != x2[i] ==> true)
        }
// </vc-spec>
// <vc-code>
{
    x2
}
// </vc-code>


}
fn main() {}