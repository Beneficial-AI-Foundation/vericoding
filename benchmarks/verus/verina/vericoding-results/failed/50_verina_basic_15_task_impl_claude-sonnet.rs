// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper lemma to establish the existence of consecutive numbers
proof fn lemma_consecutive_found(a: &Vec<i32>, idx: usize)
    requires
        idx < a.len() - 1,
        a[idx as int] + 1 == a[(idx + 1) as int],
    ensures
        exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
{
    assert(a[idx as int] + 1 == a[(idx + 1) as int]);
}

/* helper modified by LLM (iteration 5): added trigger annotation to fix quantifier trigger inference */
// Helper lemma for the negative case
proof fn lemma_no_consecutive(a: &Vec<i32>)
    requires
        forall|i: usize| i < a.len() - 1 ==> #[trigger] a[i as int] + 1 != a[(i + 1) as int],
    ensures
        !exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
{
}
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assert statement syntax for proper proof block */
    if a.len() <= 1 {
        proof {
            assert forall|i: int| !(0 <= i < a.len() - 1) by {
                assert(a.len() <= 1);
            }
        }
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            forall|j: usize| j < i ==> #[trigger] a[j as int] + 1 != a[(j + 1) as int],
        decreases a.len() - 1 - i
    {
        if a[i] + 1 == a[i + 1] {
            proof {
                lemma_consecutive_found(a, i);
            }
            return true;
        }
        i += 1;
    }
    
    proof {
        lemma_no_consecutive(a);
    }
    false
}
// </vc-code>

}
fn main() {}