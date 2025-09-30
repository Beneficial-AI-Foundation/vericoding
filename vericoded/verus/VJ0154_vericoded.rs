// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide max function and simple monotonicity lemmas for ints */
spec fn max_int(a: int, b: int) -> int { if a >= b { a } else { b } }
/* helper modified by LLM (iteration 3): lemma that max is at least a */
proof fn max_int_ge_a(a: int, b: int) ensures a <= max_int(a, b) {
    if a >= b {
        assert(max_int(a, b) == a);
    } else {
        assert(max_int(a, b) == b);
        assert(a <= b);
    }
}
/* helper modified by LLM (iteration 3): lemma that max is at least b */
proof fn max_int_ge_b(a: int, b: int) ensures b <= max_int(a, b) {
    if a >= b {
        assert(max_int(a, b) == a);
        assert(b <= a);
    } else {
        assert(max_int(a, b) == b);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed invariants casting issue and implemented iterative max index search */
    let mut best: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        invariant
            best < a.len(),
            1 <= i as int,
            i <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> a[k] <= a[best as int],
        decreases (a.len() - i) as int
    {
        if a[i] > a[best] {
            best = i;
        }
        i += 1;
    }

    best
}
// </vc-code>

}
fn main() {}