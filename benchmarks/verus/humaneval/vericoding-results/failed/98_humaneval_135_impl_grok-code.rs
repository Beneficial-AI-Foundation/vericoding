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
{ 
    /* code modified by LLM (iteration 2): fixed implementation to find the largest decrease index by scanning the array from right to left, using a loop with proper invariants to ensure no decreases occur after the identified index */ 
    let len = arr.len() as int;
    if len <= 1 {
        return -1;
    }
    let mut i = len - 1;
    while i >= 1
        invariant
            valid_input(arr@),
            1 <= i + 1 <= len,
            forall|j: int| i + 1 <= j < len ==> !has_decrease_at(arr@, j),
        decreases i
    {
        if arr[i as usize] < arr[(i - 1) as usize] {
            return i as i8;
        }
        i = i - 1;
    }
    return -1;
}
// </vc-code>


}

fn main() {}