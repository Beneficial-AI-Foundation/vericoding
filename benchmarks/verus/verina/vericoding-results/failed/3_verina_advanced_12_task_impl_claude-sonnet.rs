// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function to safely convert usize to int for sequence access */
spec fn seq_at(s: Seq<i32>, i: usize) -> i32
    requires i < s.len()
{
    s[i as int]
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
    /* code modified by LLM (iteration 5): fixed compilation error by using @ operator for sequence access instead of casting to int in exec code */
    let mut idx: usize = 0;
    while idx < lst.len()
        invariant
            0 <= idx <= lst.len(),
            forall|i: int, j: int| 0 <= i < j < idx ==> lst[i] != lst[j]
    {
        let mut prev_idx: usize = 0;
        while prev_idx < idx
            invariant
                0 <= prev_idx <= idx < lst.len(),
                forall|k: int| 0 <= k < prev_idx ==> lst[k] != lst[idx as int],
                forall|i: int, j: int| 0 <= i < j < idx ==> lst[i] != lst[j]
        {
            if lst@[prev_idx] == lst@[idx] {
                return lst@[idx];
            }
            prev_idx += 1;
        }
        idx += 1;
    }
    -1
}
// </vc-code>

}
fn main() {}