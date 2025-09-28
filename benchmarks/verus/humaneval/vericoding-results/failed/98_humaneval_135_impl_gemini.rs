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
/* helper modified by LLM (iteration 3): [helper is correct, no change needed] */
proof fn lemma_is_largest_decrease_index(arr: Seq<int>, i: int)
    requires
        has_decrease_at(arr, i),
        forall|j: int| i < j < arr.len() ==> arr[j] >= arr[j-1],
    ensures
        is_largest_decrease_index(arr, i),
{
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
{
    /* code modified by LLM (iteration 3): [added .view() for type conversion & updated invariant] */
    let n = arr.len() as int;
    if n <= 1 {
        assert(is_non_decreasing(arr@.view()));
        return -1;
    }

    let mut i = n - 1;
    while i > 0
        invariant
            0 < i < n,
            forall|j: int| i < j < n ==> arr@.view()[j] >= arr@.view()[j-1],
        decreases i
    {
        if arr[i as usize] < arr[(i - 1) as usize] {
            assert(has_decrease_at(arr@.view(), i));
            lemma_is_largest_decrease_index(arr@.view(), i);
            return i as i8;
        }
        i = i - 1;
    }

    assert(forall|j: int| 1 <= j < n ==> arr@.view()[j] >= arr@.view()[j-1]);
    assert(is_non_decreasing(arr@.view()));
    return -1;
}
// </vc-code>


}

fn main() {}