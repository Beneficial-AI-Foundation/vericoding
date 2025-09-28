// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed helper predicates and lemmas */
spec fn is_zero(a: f32) -> bool {
    a == 0.0f32
}

spec fn all_helper(a: Seq<f32>, i: int, j: int) -> bool {
    i <= j <= a.len()
    && forall|k: int| i <= k < j ==> !is_zero(a[k])
}

proof fn all_helper_lemma(a: Seq<f32>, i: int, j: int, k: int)
    requires
        all_helper(a, i, j),
        i <= k < j,
    ensures
        !is_zero(a[k])
{
}

proof fn empty_range_all_helper(a: Seq<f32>, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        all_helper(a, i, i)
{
}

proof fn extend_all_helper(a: Seq<f32>, i: int, j: int)
    requires
        all_helper(a, i, j),
        j < a.len(),
        !is_zero(a[j]),
    ensures
        all_helper(a, i, j + 1)
{
}

proof fn all_helper_implies_result(a: Seq<f32>, i: int, j: int)
    requires
        all_helper(a, i, j),
        i == 0,
        j == a.len(),
    ensures
        forall|k: int| 0 <= k < a.len() ==> !is_zero(a[k])
{
}
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32),
        (a@.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a@.len() && a@[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the loop invariant and proof helper calls */
{
    if a.len() == 0 {
        return true;
    }
    
    proof {
        empty_range_all_helper(a@, 0);
    }
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            all_helper(a@, 0, i as int),
            0 <= i <= a.len(),
        decreases a.len() - i
    {
        if a[i] == 0.0f32 {
            return false;
        }
        proof {
            extend_all_helper(a@, 0, i as int);
        }
        i = i + 1;
    }
    proof {
        all_helper_implies_result(a@, 0, a.len() as int);
    }
    true
}
// </vc-code>

}
fn main() {}