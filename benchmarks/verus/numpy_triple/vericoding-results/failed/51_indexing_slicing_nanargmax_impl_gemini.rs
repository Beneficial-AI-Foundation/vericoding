// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added transitivity lemma for f32 comparison */
spec fn is_finite(x: f32) -> bool {
    x.is_finite()
}

spec fn f32_ge(a: f32, b: f32) -> bool {
    a >= b
}

proof fn lemma_f32_ge_transitive(a: f32, b: f32, c: f32)
    requires
        f32_ge(a, b),
        f32_ge(b, c),
    ensures
        f32_ge(a, c)
{}
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed syntax error in `assert forall` */
    let mut max_idx: usize = 0;
    let mut found_finite = false;

    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            found_finite ==> max_idx < i && is_finite(a@[max_idx as int]),
            found_finite ==> forall|j: int| 0 <= j < i && is_finite(a@[j]) ==> f32_ge(a@[max_idx as int], a@[j]),
            !found_finite ==> forall|j: int| 0 <= j < i ==> !is_finite(a@[j]),
    {
        if a[i].is_finite() {
            if !found_finite || a[i] > a[max_idx] {
                found_finite = true;
                max_idx = i;
            }
        }
        i = i + 1;
    }

    proof {
        if !found_finite {
            assert forall|j: int| 0 <= j < a.len() implies !is_finite(a@[j]) by {};
            let k = choose|k: int| 0 <= k < a.len() && is_finite(a@[k]);
            assert(is_finite(a@[k]));
            assert(!is_finite(a@[k]));
            assert(false);
        }
    }

    max_idx
}
// </vc-code>

}
fn main() {}