// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_inversions(arr: Seq<nat>) -> nat
    decreases arr.len()
{
    if arr.len() <= 1 {
        0
    } else {
        let count_first: nat = arr.skip(1).filter(|x: nat| x < arr[0]).len();
        count_first + count_inversions(arr.skip(1))
    }
}

spec fn count_local_inversions(arr: Seq<nat>) -> nat
    decreases arr.len()
{
    if arr.len() <= 1 {
        0
    } else if arr.len() == 2 {
        if arr[0] > arr[1] { 1 } else { 0 }
    } else {
        let local_first: nat = if arr[0] > arr[1] { 1 } else { 0 };
        local_first + count_local_inversions(arr.skip(1))
    }
}

spec fn is_permutation(n: nat, arr: Seq<nat>) -> bool {
    arr.len() == n &&
    forall|i: nat| 1 <= i <= n ==> arr.contains(i) &&
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}
// </vc-helpers>

// <vc-spec>
fn is_good_permutation(n: nat, arr: Vec<nat>) -> (result: bool)
    requires 
        n > 0,
        arr.len() == n,
        is_permutation(n, arr@),
    ensures result == (count_inversions(arr@) == count_local_inversions(arr@))
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>

}

fn main() {
    // /* Apps difficulty: interview */
    // /* Assurance level: unguarded */
    
    // /* Test cases */
    // assert(is_good_permutation(1, vec![1]));
    // assert(is_good_permutation(2, vec![2, 1]));
    // assert(!is_good_permutation(3, vec![3, 2, 1]));
    // assert(is_good_permutation(4, vec![1, 3, 2, 4]));
}