// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added trigger annotation to quantifier in invariant */
    if a.len() <= 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= a[j + 1],
        decreases a.len() - 1 - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < a.len() - 1 ==> #[trigger] a[j] <= a[j + 1]);
    }
    
    true
}
// </vc-code>

}
fn main() {}