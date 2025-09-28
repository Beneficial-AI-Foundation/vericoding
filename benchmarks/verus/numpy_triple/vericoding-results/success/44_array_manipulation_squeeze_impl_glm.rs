// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn squeeze_lemma<T>(a: Vec<T>)
    requires a.len() == 1,
    ensures squeeze(a) == a[0]
{
    reveal(squeeze);
    assert(squeeze(a) == a[0]);
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
    /* code modified by LLM (iteration 2): removed call to proof function in executable context */
    let result = a[0];
    result
}
// </vc-code>

}
fn main() {}