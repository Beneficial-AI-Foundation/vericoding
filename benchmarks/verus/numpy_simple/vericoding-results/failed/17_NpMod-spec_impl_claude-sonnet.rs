// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn all_nonzero(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn mod_vec(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        all_nonzero(b@),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix bounds checks by casting to int */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j as int] % b@[j as int],
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(a.len() == b.len());
            assert(i < b.len());
            assert(0 <= i as int < a@.len());
            assert(0 <= i as int < b@.len());
        }
        result.push(a[i] % b[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}