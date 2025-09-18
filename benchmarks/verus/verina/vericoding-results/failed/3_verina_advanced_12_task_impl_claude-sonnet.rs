// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added predicate to check if no duplicates exist up to index */
predicate no_duplicates_until(lst: &Seq<i32>, idx: int) {
    forall|k: int, l: int| 0 <= k < l < idx ==> lst[k] != lst[l]
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
    /* code modified by LLM (iteration 5): fixed type mismatches and sequence indexing */
    let mut i: usize = 0;
    while i < lst.len() as usize
        invariant
            0 <= i <= lst.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> lst@[k] != lst@[l],
    {
        let mut j: usize = i + 1;
        while j < lst.len() as usize
            invariant
                0 <= i < lst.len(),
                i + 1 <= j <= lst.len(),
                forall|k: int, l: int| 0 <= k < l < i ==> lst@[k] != lst@[l],
                forall|l: int| i + 1 <= l < j ==> lst@[i as int] != lst@[l],
        {
            if lst@[i as int] == lst@[j as int] {
                return lst@[i as int];
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