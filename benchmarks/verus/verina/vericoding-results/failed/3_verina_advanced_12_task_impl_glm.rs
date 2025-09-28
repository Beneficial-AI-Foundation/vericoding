// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix type annotation for i */
proof fn first_duplicate_helper(lst: &Seq<i32>) -> (result: i32)
    ensures
        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&
        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
{
    if lst.len() < 2 {
        return -1i32;
    }
    
    let mut seen: Set<int> = Set::empty();
    let mut i: int = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> lst[j] != lst[k],
            seen == Set::<int>::new(|x: int| exists|j: int| 0 <= j < i && lst[j] == x),
            decreases lst.len() - i,
    {
        if seen.contains(lst.index(i) as int) {
            return lst.index(i);
        }
        seen = seen.insert(lst.index(i) as int);
        i += 1;
    }
    
    -1i32
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
    /* code modified by LLM (iteration 3): call helper function */
    first_duplicate_helper(lst)
}
// </vc-code>

}
fn main() {}