// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): placeholder repeat_seq replaced with a simple Seq constructor to avoid unsupported API */
spec fn repeat_seq<T>(fill: T, n: usize) -> Seq<T>
{
    Seq::new()
}
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
    /* code modified by LLM (iteration 5): build Vec by pushing fill_value n times and return it */
    let mut v: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|k: int| 0 <= k < i as int ==> v[k] == fill_value,
        decreases n - i
    {
        v.push(fill_value);
        proof {
            assert(v.len() == i + 1);
            assert(v[i as int] == fill_value);
        }
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}