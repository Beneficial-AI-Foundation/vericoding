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
/* helper modified by LLM (iteration 5): fixed lemma keyword syntax error */
proof fn lemma_largest_decrease_unique(arr: Seq<int>, i: int, j: int)
    requires
        is_largest_decrease_index(arr, i),
        is_largest_decrease_index(arr, j),
    ensures
        i == j,
{
}

proof fn lemma_decrease_exists_implies_not_non_decreasing(arr: Seq<int>)
    requires
        exists|i: int| has_decrease_at(arr, i),
    ensures
        !is_non_decreasing(arr),
{
}

proof fn lemma_non_decreasing_implies_no_decrease(arr: Seq<int>)
    requires
        is_non_decreasing(arr),
    ensures
        forall|i: int| !has_decrease_at(arr, i),
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
    /* code modified by LLM (iteration 5): fixed ensures clause syntax error by removing trailing comma */
    let mut result: i8 = -1;
    let mut i = (arr.len() - 1) as usize;
    
    while i > 0
        invariant
            i < arr.len(),
            result == -1 || (0 < result as int && result as int < arr@.len()),
            result == -1 ==> forall|j: int| (i as int) < j < arr@.len() ==> arr@[j] >= arr@[j-1],
            result != -1 ==> is_largest_decrease_index(arr@, result as int),
        decreases i
    {
        if arr[i] < arr[i-1] {
            result = i as i8;
        }
        i = i - 1;
    }
    
    if result == -1 {
        proof {
            assert(forall|j: int| 1 <= j < arr@.len() ==> arr@[j] >= arr@[j-1]);
        }
    } else {
        proof {
            assert(has_decrease_at(arr@, result as int));
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}