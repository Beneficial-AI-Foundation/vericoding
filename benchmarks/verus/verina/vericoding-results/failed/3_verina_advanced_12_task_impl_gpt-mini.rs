// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): duplicate predicate using &Seq indexing */
spec fn has_duplicate(lst: &Seq<i32>) -> bool { exists|i: nat, j: nat| i < j && j < lst.len() && lst[i] == lst[j] }
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
    /* code modified by LLM (iteration 5): iterate to find first element with a later duplicate using &Seq indexing */
    let n: nat = lst.len();
    if !has_duplicate(lst) {
        -1
    } else {
        let mut i: nat = 0;
        while i < n
            decreases n - i
        {
            if exists|j: nat| i < j && j < n && lst[i] == lst[j] {
                return lst[i];
            }
            i = i + 1;
        }
        -1
    }
}
// </vc-code>

}
fn main() {}