// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert usize to int */
spec fn usize_to_int(n: usize) -> int { n as int }
// </vc-helpers>

// <vc-spec>
fn full<T>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): construct Vec<T> with n copies using usize loop and proper invariants */
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        invariant result.len() == i,
        invariant forall|k: int| 0 <= k && k < (i as int) ==> result@[k] == fill_value
    {
        result.push(fill_value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}