// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_all_nan_implies_not_has_finite(a: Seq<f32>)
    requires
        all_nan(a),
    ensures
        !has_finite_value(a),
{
    if has_finite_value(a) {
        let i = choose|i: int| 0 <= i < a.len() && (a[i] == a[i]);
        assert(a[i] != a[i]);
    }
}

proof fn lemma_found_finite_implies_not_all_nan(a: Seq<f32>, i: int)
    requires
        0 <= i < a.len(),
        a[i] == a[i],
    ensures
        !all_nan(a),
{
    if all_nan(a) {
        assert(a[i] != a[i]);
    }
}

// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [added decreases clause to while loop] */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> a@[k] != a@[k],
        decreases a.len() - i
    {
        if a[i] == a[i] {
            proof {
                lemma_found_finite_implies_not_all_nan(a@, i as int);
            }
            return a[i];
        }
        i = i + 1;
    }

    proof {
        lemma_all_nan_implies_not_has_finite(a@);
    }

    0.0f32 / 0.0f32
}

// </vc-code>

}
fn main() {}