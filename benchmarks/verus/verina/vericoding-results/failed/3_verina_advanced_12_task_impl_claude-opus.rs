// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> lst[k] != lst[l],
    {
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                i < lst.len(),
                forall|k: int| 0 <= k < j ==> lst[k] != lst[i],
                forall|k: int, l: int| 0 <= k < l < i ==> lst[k] != lst[l],
        {
            if lst[j] == lst[i] {
                return lst[i];
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-code>

}
fn main() {}