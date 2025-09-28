// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_element(arr: Seq<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == elem
}

spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn in_exactly_one(ar1: Seq<i32>, ar2: Seq<i32>, elem: i32) -> bool {
    (contains_element(ar1, elem) && !contains_element(ar2, elem)) ||
    (contains_element(ar2, elem) && !contains_element(ar1, elem))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable wrapper for contains_element */
fn contains_vec(arr: &Vec<i32>, elem: i32) -> bool
    ensures
        result == contains_element(arr@, elem),
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            found == exists|k: int| 0 <= k < (i as int) && arr@[k] == elem,
        decreases arr.len() - i,
    {
        if arr[i] == elem {
            found = true;
        }
        i += 1;
    }
    proof {
        assert(found == exists|k: int| 0 <= k < arr.len() && arr@[k] == elem);
    }
    found
}

/* helper modified by LLM (iteration 5): insert element into sorted unique vector at position preserving properties */
fn insert_preserves_sorted_no_dup(seq: &mut Vec<i32>, x: i32, pos: usize)
    requires
        pos <= old(seq).len(),
        is_sorted(old(seq)@),
        has_no_duplicates(old(seq)@),
        !contains_element(old(seq)@, x),
        pos > 0 ==> old(seq)@[(pos as int) - 1] < x,
        pos < old(seq).len() ==> old(seq)@[(pos as int)] > x,
    ensures
        is_sorted(seq@),
        has_no_duplicates(seq@),
        contains_element(seq@, x),
{
    seq.insert(pos, x);
    proof {
        // After insertion, the new sequence contains x
        assert(contains_element(seq@, x));
        // x was not in old(seq) and we inserted exactly one x, so no duplicates
        assert(has_no_duplicates(seq@));
        // Insertion at the specified position preserves sortedness
        assert(is_sorted(seq@));
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_setxor1d(ar1: &Vec<i32>, ar2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* Result is sorted */
        is_sorted(result@),
        /* Result has no duplicates */
        has_no_duplicates(result@),
        /* Every element in result is from exactly one input array */
        forall|i: int| 0 <= i < result.len() ==> #[trigger] in_exactly_one(ar1@, ar2@, result[i]),
        /* Every element that appears in exactly one input array is in the result */
        forall|x: i32| in_exactly_one(ar1@, ar2@, x) ==> contains_element(result@, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): construct sorted unique symmetric difference */
{
    let mut result: Vec<i32> = Vec::new();

    // Process elements from ar1: add those that are in ar1 but not in ar2
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            is_sorted(result@),
            has_no_duplicates(result@),
            forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result[k]),
        decreases ar1.len() - i,
    {
        let x = ar1[i];
        if !contains_vec(ar2, x) && !contains_vec(&result, x) {
            // find insertion position to keep result sorted
            let mut j: usize = 0;
            while j < result.len()
                invariant
                    is_sorted(result@),
                    has_no_duplicates(result@),
                    forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result[k]),
                    forall|k: int| 0 <= k < (j as int) ==> result@[k] < x,
                decreases result.len() - j,
            {
                if result[j] >= x { break; }
                j += 1;
            }
            insert_preserves_sorted_no_dup(&mut result, x, j);
        }
        i += 1;
    }

    // Process elements from ar2: add those that are in ar2 but not in ar1
    let mut i2: usize = 0;
    while i2 < ar2.len()
        invariant
            is_sorted(result@),
            has_no_duplicates(result@),
            forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result[k]),
        decreases ar2.len() - i2,
    {
        let x = ar2[i2];
        if !contains_vec(ar1, x) && !contains_vec(&result, x) {
            let mut j: usize = 0;
            while j < result.len()
                invariant
                    is_sorted(result@),
                    has_no_duplicates(result@),
                    forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result[k]),
                    forall|k: int| 0 <= k < (j as int) ==> result@[k] < x,
                decreases result.len() - j,
            {
                if result[j] >= x { break; }
                j += 1;
            }
            insert_preserves_sorted_no_dup(&mut result, x, j);
        }
        i2 += 1;
    }

    result
}

// </vc-code>


}
fn main() {}