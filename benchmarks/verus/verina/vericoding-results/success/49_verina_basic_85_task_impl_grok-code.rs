// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added a@.len() == n to loop invariant to ensure index bounds for a[n-1-i] */
    let mut result = Vec::new();
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            a@.len() == n,
            0 <= i <= n,
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j] == a[n - 1 - j]
        decreases n - i
    {
        result.push(a[n - 1 - i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}