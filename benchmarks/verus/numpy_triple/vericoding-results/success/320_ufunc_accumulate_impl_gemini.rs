// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn accumulate(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> result[0] == a[0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added invariant to track a.len() */
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            i <= n,
            result.len() == i,
            result.view() == a.view().take(i as int),
        decreases n - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}