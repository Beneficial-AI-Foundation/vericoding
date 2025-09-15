// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added boundary check helper for safe indexing */
spec fn valid_index_pair(len: int, i: int) -> bool {
    0 <= i < len - 1
}
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking by ensuring i+1 is valid */
    if a.len() <= 1 {
        return true;
    }
    
    for i in 0..a.len() - 1
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= a@[j + 1],
            i <= a.len() - 1
    {
        assert(i < a.len() - 1);
        assert(i + 1 < a.len());
        if a[i] > a[i + 1] {
            return false;
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}