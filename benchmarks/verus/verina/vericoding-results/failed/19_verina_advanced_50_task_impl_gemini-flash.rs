// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This section is empty as no helpers are necessary. */
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous errors were mismatched types related to array indexing and comparison; `a1[i]` and `a2[j]` were passed as usize instead of nat where needed. Corrected by casting the values to `nat` explicitly. */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < a1.len() || j < a2.len()
        invariant
            0 <= i && i <= a1.len(),
            0 <= j && j <= a2.len(),
            result@.len() == i + j,
            is_sorted(result@),
            result@.to_multiset().add(a1@.subrange(i as int, a1@.len() as int).to_multiset()).add(a2@.subrange(j as int, a2@.len() as int).to_multiset()) == a1@.to_multiset().add(a2@.to_multiset()),

        decreases (a1.len() - i) + (a2.len() - j)
    {
        if i < a1.len() && (j == a2.len() || a1[i] <= a2[j]) {
            if result.len() > 0 {
                proof {
                    assert(0 <= result.len()-1);
                    assert((result.len()-1) < result.len());
                    assert(result[result.len()-1] <= a1[i] as nat);
                }
            }
            result.push(a1[i]);
            i = i + 1;
        } else if j < a2.len() && (i == a1.len() || a2[j] < a1[i]) {
            if result.len() > 0 {
                proof {
                    assert(0 <= result.len()-1);
                    assert((result.len()-1) < result.len());
                    assert(result[result.len()-1] <= a2[j] as nat);
                }
            }
            result.push(a2[j]);
            j = j + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}