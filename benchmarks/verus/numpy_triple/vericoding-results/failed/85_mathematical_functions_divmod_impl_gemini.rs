// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no change */
fn integer_divmod(x: i32, d: i32) -> (res: (i32, i32))
    requires d != 0
    ensures
        x == d * res.0 + res.1,
        d > 0 ==> 0 <= res.1 < d,
        d < 0 ==> d < res.1 <= 0,
{
    let q_raw = x / d;
    let r_raw = x % d;
    
    if (d > 0 && r_raw < 0) || (d < 0 && r_raw > 0) {
        (q_raw - 1, r_raw + d)
    } else {
        (q_raw, r_raw)
    }
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
{
    /* code modified by LLM (iteration 4): added decreases clause to loop to prove termination */
    let mut quotient: Vec<i32> = Vec::new();
    let mut remainder: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < x2.len() ==> x2@[j] != 0,
            quotient.len() == i,
            remainder.len() == i,
            forall|j: int| 0 <= j < i ==> {
                x1@[j] == x2@[j] * quotient@[j] + remainder@[j] &&
                (x2@[j] > 0 ==> 0 <= remainder@[j] && remainder@[j] < x2@[j]) &&
                (x2@[j] < 0 ==> x2@[j] < remainder@[j] && remainder@[j] <= 0)
            },
        decreases x1.len() - i
    {
        let (q, r) = integer_divmod(x1[i], x2[i]);
        quotient.push(q);
        remainder.push(r);
        i = i + 1;
    }

    (quotient, remainder)
}
// </vc-code>

}
fn main() {}