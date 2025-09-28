// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn squeeze_exec_lemma<T>(a: Vec<T>, b: Vec<T>)
    requires
        a.len() == 1,
        b.len() == 1,
        squeeze(a) == squeeze(b)
    ensures a[0] == b[0]
{
    assert(a@[0] == squeeze(a));
    assert(b@[0] == squeeze(b));
}

proof fn squeeze_same_elem_lemma<T>(a: Vec<T>, i: int)
    requires
        0 <= i < a.len(),
        a.len() == 1
    ensures
        a@[i] == a@[0]
{
}

// </vc-helpers>

// <vc-spec>
spec fn squeeze<T>(a: Vec<T>) -> T
    recommends a.len() == 1
{
    a[0]
}

fn squeeze_exec<T: Copy>(a: Vec<T>) -> (result: T)
    requires a.len() == 1,
    ensures 
        result == squeeze(a),
        result == a[0],
        forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0],
        forall|i: int| 0 <= i < a.len() ==> a[i] == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed implementation using proper sequence syntax and validation */
    let result = a[0];
    proof {
        assert(squeeze(a) == a@[0]);
        
        assert forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) implies a@[0] == b@[0] by {
            squeeze_exec_lemma(a, b);
        };
        
        assert forall|i: int| 0 <= i < a.len() implies a@[i] == result by {
            if 0 <= i < a.len() {
                squeeze_same_elem_lemma(a, i);
            }
        };
    }
    result
}
// </vc-code>

}
fn main() {}