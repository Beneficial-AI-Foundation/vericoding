// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_value(seq: &Seq<i32>, val: i32, start: usize, end: usize) -> (found: bool)
    requires
        start <= end && end as int <= seq.len()
    ensures
        found <==> (exists|k: int| start as int <= k < end as int && seq@[k] == val)
{
    spec fn contains_value_inner(sq: Seq<i32>, st: usize, en: usize) -> bool {
        if st >= en {
            false
        } else if sq[st as int] == val {
            true
        } else {
            contains_value_inner(sq, st + 1, en)
        }
    }
    contains_value_inner(seq@, start, end)
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
/* code modified by LLM (iteration 5): changed i to usize and used as int for indexing and casts */
{
    let mut i: usize = 0;
    while i < (lst.len() as usize)
        invariant
            0 <= i <= lst.len() as usize
    {
        if contains_value(lst, lst@[i as int], i + 1, lst.len() as usize) {
            return lst@[i as int];
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}