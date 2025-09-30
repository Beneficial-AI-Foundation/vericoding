// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_equal_to_first(s: Seq<i32>) -> bool { forall|i: int| 1 <= i < s.len() ==> s[0] == #[trigger] s[i] }
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)

    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut res: bool = true;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            res == (forall|j: int| 1 <= j < i as int ==> arr[0] == #[trigger] arr[j]),
            n as int == arr@.len(),
        decreases n as int - i as int
    {
        let a0 = arr[0];
        let ai = arr[i];
        if a0 != ai {
            res = false;
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}