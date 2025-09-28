// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn next_val_helper(v1: i8, v2: i8) -> (res: i8)
    ensures
        (v1 == v2 ==> res == v1),
        (v1 < v2 ==> v1 < res && res <= v2),
        (v1 > v2 ==> v1 > res && res >= v2),
{
    if v1 < v2 {
        v1 + 1
    } else if v1 > v2 {
        v1 - 1
    } else {
        v1
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
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> {
                (x1@[j] == x2@[j] ==> result@[j] == x1@[j]) &&
                ((x1@[j] < x2@[j] ==> x1@[j] < result@[j] && result@[j] <= x2@[j]) &&
                 (x1@[j] > x2@[j] ==> x1@[j] > result@[j] && result@[j] >= x2@[j])) &&
                (x1@[j] != x2@[j] ==> true)
            },
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        let next = next_val_helper(val1, val2);
        result.push(next);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}