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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            a.len() == b.len(),
            result.len() == i,
            all_nonzero(b@),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
            0 <= i && i <= a.len(),
        decreases a.len() - i
    {
        //@ assume(b@[i] != 0);
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}