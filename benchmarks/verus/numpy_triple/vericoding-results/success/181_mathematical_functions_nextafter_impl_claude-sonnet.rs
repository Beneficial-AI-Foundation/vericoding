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
    /* code modified by LLM (iteration 5): fixed bounds checking with proper casts and loop structure */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> {
                (x1[j] == x2[j] ==> result[j] == x1[j]) &&
                ((x1[j] < x2[j] ==> x1[j] < result[j] && result[j] <= x2[j]) &&
                 (x1[j] > x2[j] ==> x1[j] > result[j] && result[j] >= x2[j])) &&
                (x1[j] != x2[j] ==> true)
            },
        decreases x1.len() - i
    {
        let idx = i as usize;
        let next_val = if x1[idx] == x2[idx] {
            x1[idx]
        } else if x1[idx] < x2[idx] {
            if x1[idx] == i8::MAX {
                x1[idx]
            } else {
                x1[idx] + 1
            }
        } else {
            if x1[idx] == i8::MIN {
                x1[idx]
            } else {
                x1[idx] - 1
            }
        };
        result.push(next_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}