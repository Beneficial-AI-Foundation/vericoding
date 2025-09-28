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
proof {
    let mut seen = Set::empty();
    let mut i: int = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            seen =~= Set::new(|k: i32| exists |j: int| 0 <= j < i && k == lst[j])
        decreases lst.len() - i
    {
        if (seen.contains(lst.index(i))) {
            return lst.index(i);
        }
        seen = seen.insert(lst.index(i));
        i = i + 1;
    }
    return -1;
}
// </vc-code>

}
fn main() {}