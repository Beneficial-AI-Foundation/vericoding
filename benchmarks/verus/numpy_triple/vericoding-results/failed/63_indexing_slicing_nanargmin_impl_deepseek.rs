// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove duplicate spec function definitions and add uninterp annotation */
uninterp spec fn f32_is_nan(x: f32) -> bool;

uninterp spec fn f32_le(a: f32, b: f32) -> bool;

proof fn lemma_min_index_property(s: Seq<f32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        !f32_is_nan(s[i]),
        !f32_is_nan(s[j]),
        f32_le(s[i], s[j]),
        f32_le(s[j], s[i]),
    ensures
        i <= j,
{
}

proof fn lemma_compare_nans(s: Seq<f32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        f32_is_nan(s[i]),
        !f32_is_nan(s[j]),
    ensures
        true,
{
}

spec fn is_min_index(s: Seq<f32>, idx: int) -> bool
{
    forall|j: int| 0 <= j < s.len() && !f32_is_nan(s[j]) ==> f32_le(s[idx], s[j])
}

spec fn find_first_min(s: Seq<f32>, idx: int) -> bool
{
    is_min_index(s, idx) && (forall|j: int| 0 <= j < s.len() && !f32_is_nan(s[j]) && is_min_index(s, j) ==> idx <= j)
}
// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Main implementation with proper loop invariants */
    let mut min_idx = 0;
    let mut found_valid = false;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            min_idx < a.len(),
            found_valid ==> (!f32_is_nan(a[min_idx as int]) && (forall|j: int| 0 <= j < i && !f32_is_nan(a[j]) ==> f32_le(a[min_idx as int], a[j]))),
            !found_valid ==> (0 <= min_idx < i ==> f32_is_nan(a[min_idx as int])),
        decreases a.len() - i,
    {
        if !f32_is_nan(a[i]) {
            if !found_valid {
                min_idx = i;
                found_valid = true;
            } else if f32_le(a[i], a[min_idx]) {
                if f32_le(a[min_idx], a[i]) {
                    proof {
                        lemma_min_index_property(a@, min_idx as int, i as int);
                    }
                    if i < min_idx {
                        min_idx = i;
                    }
                } else {
                    min_idx = i;
                }
            }
        }
        i += 1;
    }
    
    min_idx
}
// </vc-code>

}
fn main() {}