// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): carried over spec helpers, which are not used by the new exec code but are logically sound */
spec fn has_prior_occurrence(lst: Seq<i32>, j: int) -> bool
{
    exists|i: int| 0 <= i < j && lst[i] == lst[j]
}

spec fn find_first_duplicate_idx(lst: Seq<i32>, start_idx: int) -> (res: int)
    requires 0 <= start_idx <= lst.len(),
    ensures
        (res == -1 ==> (forall|k: int| start_idx <= k < lst.len() ==> !has_prior_occurrence(lst, k))),
        (res != -1 ==> (
            start_idx <= res < lst.len() &&
            has_prior_occurrence(lst, res) &&
            forall|k: int| start_idx <= k < res ==> !has_prior_occurrence(lst, k)
        )),
    decreases lst.len() - start_idx
{
    if start_idx >= lst.len() {
        -1
    } else if has_prior_occurrence(lst, start_idx) {
        start_idx
    } else {
        find_first_duplicate_idx(lst, start_idx + 1)
    }
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
    /* code modified by LLM (iteration 5): implemented an executable nested loop algorithm and proved its correctness via invariants */
    let mut j: usize = 0;
    while j < lst.len()
        invariant
            0 <= j <= lst.len(),
            forall|k: int, l: int| 0 <= k < l < (j as int) ==> lst@[k] != lst@[l],
    {
        let mut i: usize = 0;
        while i < j
            invariant
                0 <= j < lst.len(),
                forall|k: int, l: int| 0 <= k < l < (j as int) ==> lst@[k] != lst@[l],
                0 <= i <= j,
                forall|k: int| 0 <= k < (i as int) ==> lst@[k] != lst@[j as int],
        {
            if lst[i] == lst[j] {
                return lst[j];
            }
            i = i + 1;
        }
        j = j + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}