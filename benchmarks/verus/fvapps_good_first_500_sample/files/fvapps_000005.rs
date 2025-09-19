// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn contains_all_from_1_to_n(arr: Seq<i32>, n: i32) -> bool {
    forall|i: i32| 1 <= i <= n ==> #[trigger] arr.contains(i)
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> #[trigger] arr[i] != #[trigger] arr[j]
}

spec fn is_permutation(arr: Seq<i32>, n: i32) -> bool {
    arr.len() == n &&
    contains_all_from_1_to_n(arr, n) &&
    has_no_duplicates(arr) &&
    forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= n
}

spec fn is_valid_split(arr: Seq<i32>, l1: usize, l2: usize) -> bool {
    l1 > 0 && l2 > 0 && l1 + l2 == arr.len() &&
    is_permutation(arr.take(l1 as int), l1 as i32) &&
    is_permutation(arr.skip(l1 as int), l2 as i32)
}

fn find_permutations(arr: Vec<i32>) -> (result: Vec<(usize, usize)>)
    requires 
        arr.len() >= 2,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] > 0,
    ensures
        forall|i: int| 0 <= i < result.len() ==> {
            #[trigger] result[i].0 > 0 && #[trigger] result[i].1 > 0 && 
            result[i].0 + result[i].1 == arr.len() &&
            is_valid_split(arr@, result[i].0, result[i].1)
        },
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}