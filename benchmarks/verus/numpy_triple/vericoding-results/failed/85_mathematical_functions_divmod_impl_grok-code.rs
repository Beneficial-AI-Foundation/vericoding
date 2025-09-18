// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed return type to simple tuple and updated ensures to use result.0 and result.1 */
fn divmod_pair(x: i32, y: i32) -> (i32, i32)
    requires
        y != 0,
        (y != -1) || (x != i32::MIN),
    ensures x == y * result.0 + result.1,
    ensures (y > 0 ==> 0 <= result.1 < y),
    ensures (y < 0 ==> y < result.1 <= 0)
{
    let x64: i64 = x as i64;
    let y64: i64 = y as i64;
    let mut q: i64 = x64 / y64;
    let mut r: i64 = x64 % y64;
    if y64 > 0 && r < 0 {
        r += y64;
        q -= 1;
    } else if y64 < 0 && r > 0 {
        r += y64;
        q -= 1;
    }
    (q as i32, r as i32)
}
// </vc-helpers>

// <vc-spec>
fn divmod(x1: Vec<i32>, x2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures ({
        let (quotient, remainder) = result;
        quotient.len() == x1.len() &&
        remainder.len() == x1.len() &&
        forall|i: int| 0 <= i < x1.len() ==> {
            x1[i] == x2[i] * quotient[i] + remainder[i] &&
            (x2[i] > 0 ==> 0 <= remainder[i] && remainder[i] < x2[i]) &&
            (x2[i] < 0 ==> x2[i] < remainder[i] && remainder[i] <= 0)
        }
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added loop invariant to prove lengths and properties */
{
    let mut quotient = Vec::<i32>::new();
    let mut remainder = Vec::<i32>::new();
    let len = x1.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            quotient.len() == i,
            remainder.len() == i,
            forall|j: int| 0 <= j < i ==> x1@[j] == x2@[j] * quotient@[j] + remainder@[j] &&
                (x2@[j] > 0 ==> 0 <= remainder@[j] < x2@[j]) &&
                (x2@[j] < 0 ==> x2@[j] < remainder@[j] <= 0)
    {
        let (q, r) = divmod_pair(x1[i], x2[i]);
        quotient.push(q);
        remainder.push(r);
        i += 1;
    }
    (quotient, remainder)
}
// </vc-code>

}
fn main() {}