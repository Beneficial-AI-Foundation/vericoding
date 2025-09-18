// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

spec fn squeeze_lemma_helper<T>(a: Vec<T>, b: Vec<T>) -> bool
decreases a.len() + b.len(),
{
a.len() == 1 && b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0]
}

proof fn squeeze_elem_consistency<T>(a: Vec<T>, i: int)
requires
0 <= i < a.len(),
a.len() == 1,
ensures
a[i] == squeeze(a),
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
    proof {
        squeeze_elem_consistency(a, 0);
    }
    let result = a[0];
    result
}
// </vc-code>

}
fn main() {}