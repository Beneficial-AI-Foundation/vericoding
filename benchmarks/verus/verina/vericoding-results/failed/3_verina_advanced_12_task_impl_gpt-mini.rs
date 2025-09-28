// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper that finds first duplicate from index i */
spec fn find_from(lst: &Seq<i32>, i: int) -> (result: i32)
    requires 0 <= i && i <= lst.len()
    ensures
        (result == -1_i32 ==> forall|k: int, l: int| i <= k < l < lst.len() ==> lst[k] != lst[l]) &&
        (result != -1_i32 ==>
            exists|a: int, b: int| i <= a < b < lst.len() && lst[a] == lst[b] && lst[a] == result &&
            forall|k: int, l: int| i <= k < l < lst.len() && lst[k] == lst[l] && l <= a ==> k >= a
        ),
    decreases lst.len() - i
{
    if i >= lst.len() {
        -1_i32
    } else {
        if exists|j: int| i < j < lst.len() && lst[i] == lst[j] {
            lst[i]
        } else {
            find_from(lst, i + 1)
        }
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
    /* code modified by LLM (iteration 5): call spec helper find_from starting from index 0 */
    let result: i32 = find_from(lst, 0);
    result
}
// </vc-code>

}
fn main() {}