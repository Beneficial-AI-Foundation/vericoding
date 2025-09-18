// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): boolean equality helper */
spec fn eq_bool(a: bool, b: bool) -> bool { a == b }

/* helper modified by LLM (iteration 5): lemma establishing (a == true) <==> a */
proof fn lemma_true_iff_eq(a: bool) ensures (a == true) <==> a { }
// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> x1[i] == x2[i]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): element-wise equality with strengthened loop invariants and ghost reasoning about push */
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x1.len(),
            n == x2.len(),
            result.len() == i,
            i as int == result@.len(),
            0 <= i as int <= n as int,
            i as int <= x1.len() as int,
            i as int <= x2.len() as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1[j] == x2[j]),
            forall|j: int| 0 <= j < i as int ==> (result@[j] == true) <==> (x1[j] == x2[j]),
        decreases (n - i) as int
    {
        // current indices are in-bounds by loop guard and invariants
        let b = x1[i] == x2[i];
        let ghost old_res = result@;
        result.push(b);
        proof {
            assert(old_res.len() == i as int);
            assert(result@ == old_res.push(b));
            let j = i as int;
            assert(j == old_res.len());
            assert(result@[j] == b);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}