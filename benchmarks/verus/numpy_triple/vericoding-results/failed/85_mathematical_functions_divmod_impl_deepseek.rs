// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures clause to use return values */
fn safe_div(a: i32, d: i32) -> (q: i32, r: i32)
    requires d != 0
    ensures a == d * q + r && (d > 0 ==> 0 <= r && r < d) && (d < 0 ==> d < r && r <= 0)
{
    let mut q = a / d;
    let mut r = a % d;
    
    if d > 0 && r < 0 {
        q -= 1;
        r += d;
    } else if d < 0 && r > 0 {
        q -= 1;
        r += d;
    }
    
    (q, r)
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
/* code modified by LLM (iteration 5): no changes needed to iteration 4 code */
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            quotient.len() == i,
            remainder.len() == i,
            forall|j: int| 0 <= j < i ==> {
                x1@[j] == x2@[j] * quotient@[j] + remainder@[j] &&
                (x2@[j] > 0 ==> 0 <= remainder@[j] && remainder@[j] < x2@[j]) &&
                (x2@[j] < 0 ==> x2@[j] < remainder@[j] && remainder@[j] <= 0)
            }
    {
        let (q, r) = safe_div(x1[i], x2[i]);
        quotient.push(q);
        remainder.push(r);
        i += 1;
    }
    
    (quotient, remainder)
}
// </vc-code>

}
fn main() {}