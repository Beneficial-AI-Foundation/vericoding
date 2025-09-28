// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): noop helper retained for proof structure */
fn helper_noop() { }

// </vc-helpers>

// <vc-spec>
fn ones(n: usize) -> (result: Vec<i8>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] as int == 1,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],
        forall|i: int| 0 <= i < n ==> result[i] as int > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build vector of ones with loop invariant ensuring length equals i and i <= n */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|k: int| 0 <= k < i as int ==> v@[k] as int == 1,
            i <= n,
        decreases n - i
    {
        v.push(1);
        i += 1;
    }
    v
}

// </vc-code>


}
fn main() {}