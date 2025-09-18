// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn bool_true_or_false(b: bool)
    ensures
        b == true || b == false
{
    match b {
        true => { },
        false => { },
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> out[j] == (x1[j] == x2[j])
        decreases n - i
    {
        let b = x1[i] == x2[i];
        out.push(b);
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < out.len() implies out[j] == true || out[j] == false by {
            if 0 <= j && j < out.len() {
                bool_true_or_false(out[j]);
            }
        }
    }
    out
}
// </vc-code>

}
fn main() {}