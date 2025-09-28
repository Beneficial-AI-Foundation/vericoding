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
proof fn lemma_decrease_exists(arr: Seq<int>) -> (index: int)
    requires
        !is_non_decreasing(arr),
        arr.len() > 0,
    ensures
        1 <= index < arr.len(),
        has_decrease_at(arr, index),
        forall|j: int| index < j < arr.len() ==> arr[j] >= arr[j-1],
{
    let n = arr.len();
    
    let mut i: int = n - 1;
    while i >= 1
        invariant
            1 <= i <= n,
            forall|j: int| i <= j < n ==> arr[j] >= arr[j-1],
    {
        if arr[i] < arr[i-1] {
            return i;
        }
        i = i - 1;
    }
    assert(false);
    1
}

proof fn lemma_no_decrease_implies_non_decreasing(arr: Seq<int>)
    ensures
        (forall|i: int| 1 <= i < arr.len() ==> arr[i] >= arr[i-1]) ==> is_non_decreasing(arr),
{
    assert(forall|i: int| 1 <= i < arr.len() ==> arr[i] >= arr[i-1] ==> is_non_decreasing(arr));
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
    /* code modified by LLM (iteration 5): Fix compilation error by removing invalid cast */
    let n = arr.len();
    if n <= 1 {
        return -1;
    }
    
    let mut i: int = (n - 1) as int;
    while i >= 1
        invariant
            1 <= i <= n,
            forall|j: int| i <= j < n ==> arr@[j] >= arr@[j-1],
    {
        if arr[i as usize] < arr[(i - 1) as usize] {
            return i as i8;
        }
        i = i - 1;
    }
    
    proof {
        lemma_no_decrease_implies_non_decreasing(arr@);
    }
    
    -1
}
// </vc-code>


}

fn main() {}