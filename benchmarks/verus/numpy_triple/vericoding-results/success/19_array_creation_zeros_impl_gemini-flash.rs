// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == 0,
        forall|v: Vec<i32>, i: int| 
            v.len() == n && 0 <= i < n ==> 
            result[i] + v[i] == v[i] && v[i] + result[i] == v[i],
        forall|scalar: i32, i: int| 
            0 <= i < n ==> #[trigger] (scalar * result[i]) == 0,
        forall|v: Vec<i32>, i: int| 
            v.len() == n && 0 <= i < n ==> #[trigger] (result[i] * v[i]) == 0,
        n > 0 ==> result[0] == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added a `decreases` clause to the `while` loop to satisfy the Verus verifier. The loop decreases `n - i` in each iteration. */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == 0,
        decreases n - i
    {
        result.push(0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}