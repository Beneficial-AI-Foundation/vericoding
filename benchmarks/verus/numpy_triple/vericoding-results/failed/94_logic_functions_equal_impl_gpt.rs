// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma that any bool is either true or false */
proof fn bool_is_true_or_false(b: bool)
    ensures
        b == true || b == false,
{
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
    /* code modified by LLM (iteration 5): implement element-wise equality without bypasses using a loop and invariants */
    let n = x1.len();
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> out[j] == (x1[j] == x2[j]),
            forall|j: int| 0 <= j < i as int ==> (out[j] == true || out[j] == false),
        decreases n - i
    {
        let b = x1[i] == x2[i];
        proof { bool_is_true_or_false(b); }
        out.push(b);
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}