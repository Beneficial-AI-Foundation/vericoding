// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
proof fn lemma_all_equal_from_prefix(s: Seq<i32>, first: i32)
    requires
        forall|k: int| 0 <= k < s.len() ==> s[k] == first,
    ensures
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j],
{
}
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mismatched types in assert by using spec indexing and casting */
    if a.len() <= 1 {
        return true;
    }

    let first_element = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            a.len() > 1,
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == first_element,
        decreases a.len() - i
    {
        if a[i] != first_element {
            proof {
                assert(a@[i as int] != a@[0]);
            }
            return false;
        }
        i = i + 1;
    }

    proof {
        lemma_all_equal_from_prefix(a.view(), first_element);
    }
    true
}
// </vc-code>

}
fn main() {}