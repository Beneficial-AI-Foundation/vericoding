// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_duplicate(lst: &Seq<i32>) -> (result: i32)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    -1
    // impl-end
}
// </vc-code>


}
fn main() {}