// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
}

spec fn has_decrease_at(arr: Seq<int>, i: int) -> bool {
    1 <= i < arr.len() && arr[i] < arr[i-1]
}

spec fn is_largest_decrease_index(arr: Seq<int>, result: int) -> bool {
    has_decrease_at(arr, result) && 
    (forall|j: int| #[trigger] arr.index(j) >= 0 && result < j < arr.len() ==> arr.index(j) >= arr.index(j-1))
}

spec fn is_non_decreasing(arr: Seq<int>) -> bool {
    forall|i: int| #[trigger] arr.index(i) >= 0 && 1 <= i < arr.len() ==> arr.index(i) >= arr.index(i-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in ensures clause */
fn find_largest_decrease_index(arr: Vec<i8>) -> (result: i8)
    requires
        valid_input(arr@),
    ensures
        result == -1 || (0 < result as int && result as int < arr.len() as int),
        result == -1 ==> is_non_decreasing(arr@),
        result != -1 ==> is_largest_decrease_index(arr@, result as int),
        result != -1 ==> (exists|i: int| has_decrease_at(arr@, i)),
{
    let n = arr.len();
    if n == 0 {
        return -1;
    }
    let mut i = n - 1;
    while i >= 1
        invariant
            0 <= i <= n,
            (forall|j: int| i < j < n ==> arr@[j] >= arr@[j-1]),
        decreases i
    {
        if arr[i] < arr[i-1] {
            return i as i8;
        }
        i -= 1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
fn can_arrange(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(arr@),
    ensures 
        result == -1 || (0 < result as int && result as int < arr.len()),
        result == -1 ==> is_non_decreasing(arr@),
        result != -1 ==> is_largest_decrease_index(arr@, result as int),
        result != -1 ==> (exists|i: int| has_decrease_at(arr@, i)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed syntax error in ensures clause */
{
    let n = arr.len();
    if n == 0 {
        return -1;
    }
    let mut i = n - 1;
    while i >= 1
        invariant
            0 <= i <= n,
            (forall|j: int| i < j < n ==> arr@[j] >= arr@[j-1]),
        decreases i
    {
        if arr[i] < arr[i-1] {
            return i as i8;
        }
        i -= 1;
    }
    return -1;
}
// </vc-code>


}

fn main() {}