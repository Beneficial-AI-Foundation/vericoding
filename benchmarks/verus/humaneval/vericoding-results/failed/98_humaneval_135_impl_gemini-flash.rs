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
    /* code modified by LLM (iteration 5): Fixed `result as int < arr.len()` in invariant and removed unnecessary parenthesis */
    let mut i: int = (arr.len() as int) - 1;
    let mut result: i8 = -1;

    while i >= 1
        invariant
            0 <= i,
            i <= arr.len(),
            (result == -1) || (0 <= result as int && result as int < arr.len()),
            result != -1 ==> has_decrease_at(arr@, result as int),
            result != -1 ==> (forall|k: int|
                #[trigger] arr.index(k) >= 0 && result < k < arr.len()
                ==> arr.index(k) >= arr.index(k-1)),
            forall|l: int|
                #[trigger] arr.index(l) >= 0 && i < l < arr.len()
                ==> arr.index(l) >= arr.index(l-1),
        decreases i
    {
        if arr.index(i as nat) < arr.index((i - 1) as nat) {
            result = i as i8;
            // if we found a decrease, this is the largest because we are iterating backwards
            // so we can exit
            break;
        } else {
            i = i - 1;
        }
    }
    result
}
// </vc-code>


}

fn main() {}