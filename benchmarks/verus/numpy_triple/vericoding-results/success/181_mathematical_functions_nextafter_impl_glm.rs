// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed type annotation issue */
fn next_value(a: i8, b: i8) -> (r: i8)
    ensures
        a == b ==> r == a,
        a < b ==> a < r && r <= b,
        a > b ==> a > r && r >= b
{
    if a == b {
        a
    } else if a < b {
        a + 1
    } else {
        a - 1
    }
}
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
/* code modified by LLM (iteration 5): fixed type annotation in invariant */
{
    let n = x1.len();
    let mut result = Vec::with_capacity(n);
    for i in 0..n
        invariant
            0 <= i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> {
                let a = #[trigger] x1[j];
                let b = #[trigger] x2[j];
                let r: i8 = #[trigger] result[j];
                (a == b ==> r == a) &&
                (a < b ==> a < r && r <= b) &&
                (a > b ==> a > r && r >= b)
            }
    {
        let a = x1[i];
        let b = x2[i];
        let r = next_value(a, b);
        result.push(r);
    }
    result
}
// </vc-code>


}
fn main() {}