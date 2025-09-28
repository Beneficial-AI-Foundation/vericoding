// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            i == result.len(),
            result.len() <= a.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == a[j] as int + b[j] as int,
        decreases n - i
    {
        let sum = (a[i] as i32 + b[i] as i32) as i8;
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}