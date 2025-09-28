// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count_less */
    spec fn count_less(arr: Seq<i32>, x: i32) -> nat
        decreases arr.len()
    {
        if arr.len() == 0 {
            0nat
        } else {
            let first: nat = if arr[0] < x { 1nat } else { 0nat };
            first + count_less(arr.skip(1), x)
        }
    }

    /* helper modified by LLM (iteration 5): count_le */
    spec fn count_le(arr: Seq<i32>, x: i32) -> nat
        decreases arr.len()
    {
        if arr.len() == 0 {
            0nat
        } else {
            let first: nat = if arr[0] <= x { 1nat } else { 0nat };
            first + count_le(arr.skip(1), x)
        }
    }
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn count_occurrences(arr: Seq<i32>, x: i32) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0nat
    } else {
        let first_count: nat = if arr[0] == x { 1nat } else { 0nat };
        first_count + count_occurrences(arr.skip(1), x)
    }
}

spec fn multiset_equal(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    arr1.len() == arr2.len() &&
    forall|x: i32| count_occurrences(arr1, x) == count_occurrences(arr2, x)
}

fn partition(arr: Vec<i32>, kth: usize) -> (result: Vec<i32>)
    requires kth < arr.len(),
    ensures
        result.len() == arr.len(),
        /* All elements before kth are <= the kth element */
        forall|i: int| 0 <= i < kth as int ==> result@[i] <= result@[kth as int],
        /* All elements after kth are >= the kth element */
        forall|i: int| (kth as int) < i < (result@.len()) ==> result@[i] >= result@[kth as int],
        /* The k-th element is in its correct sorted position relative to the original array */
        exists|sorted: Seq<i32>| 
            is_sorted(sorted) &&
            multiset_equal(sorted, arr@) &&
            result@[kth as int] == sorted[kth as int],
        /* The result contains the same elements as the original (multiset equality) */
        multiset_equal(result@, arr@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection sort based partitioning with manual swap to avoid complex &mut borrows */
    let mut result = arr.clone();
    let n = result.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall |p: int, q: int| 0 <= p < q < i as int ==> result@[p] <= result@[q],
        decreases n - i
    {
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                j <= n,
                i <= m && m < j,
                forall |k: int| i as int <= k < j as int ==> result@[m as int] <= result@[k],
            decreases n - j
        {
            if result[j] < result[m] {
                m = j;
            }
            j += 1;
        }
        let ii = i;
        let mm = m;
        let tmp = result[ii];
        result[ii] = result[mm];
        result[mm] = tmp;
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}