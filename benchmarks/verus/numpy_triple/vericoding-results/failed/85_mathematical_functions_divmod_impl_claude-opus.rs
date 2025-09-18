// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type error by casting usize to int for array indexing */
    let mut quotient: Vec<i32> = Vec::new();
    let mut remainder: Vec<i32> = Vec::new();
    let n = x1.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            i == quotient.len(),
            i == remainder.len(),
            n == x1.len(),
            n == x2.len(),
            forall|j: int| 0 <= j < n ==> x2[j] != 0,
            forall|j: int| 0 <= j < i ==> {
                x1[j] == x2[j] * quotient[j] + remainder[j] &&
                (x2[j] > 0 ==> 0 <= remainder[j] && remainder[j] < x2[j]) &&
                (x2[j] < 0 ==> x2[j] < remainder[j] && remainder[j] <= 0)
            },
        decreases n - i
    {
        assert(0 <= i < n);
        assert(x2[i as int] != 0);
        
        let q = x1[i] / x2[i];
        let r = x1[i] % x2[i];
        
        quotient.push(q);
        remainder.push(r);
        
        i = i + 1;
    }
    
    (quotient, remainder)
}
// </vc-code>

}
fn main() {}