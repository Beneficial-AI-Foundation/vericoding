// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic helper functions */
spec fn has_duplicate_at_or_before(lst: &Seq<i32>, pos: int) -> bool {
    exists|i: int, j: int| 0 <= i < j <= pos && j < lst.len() && lst[i] == lst[j]
}

spec fn is_first_duplicate(lst: &Seq<i32>, val: i32) -> bool {
    exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == val &&
        forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l < j ==> false
}
// </vc-helpers>

// <vc-spec>
fn first_duplicate(lst: &Seq<i32>) -> (result: i32)
    ensures

        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&

        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use direct indexing without converting to Vec */
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|p: int, q: int| 0 <= p < q < i ==> lst[p] != lst[q]
    {
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                i < lst.len(),
                forall|k: int| 0 <= k < j ==> lst[k] != lst[i as int]
        {
            if lst[j as int] == lst[i as int] {
                return lst[i as int];
            }
            j += 1;
        }
        i += 1;
    }
    -1
}
// </vc-code>

}
fn main() {}