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
proof fn lemma_sorted_insert(arr: Seq<i32>, elem: i32, pos: int)
    requires
        is_sorted(arr),
        0 <= pos <= arr.len(),
        forall|i: int| 0 <= i < pos ==> arr[i] <= elem,
        forall|i: int| pos <= i < arr.len() ==> elem <= arr[i]
    ensures
        is_sorted(arr.insert(pos, elem))
{
}

proof fn lemma_no_duplicates_insert(arr: Seq<i32>, elem: i32, pos: int)
    requires
        has_no_duplicates(arr),
        !contains_element(arr, elem),
        0 <= pos <= arr.len()
    ensures
        has_no_duplicates(arr.insert(pos, elem))
{
}

/* helper modified by LLM (iteration 5): fixed binary search invariants */
fn find_insert_position(sorted_vec: &Vec<i32>, elem: i32) -> (pos: usize)
    requires
        is_sorted(sorted_vec@)
    ensures
        pos <= sorted_vec.len(),
        forall|i: int| 0 <= i < pos ==> sorted_vec[i] <= elem,
        forall|i: int| pos <= i < sorted_vec.len() ==> elem <= sorted_vec[i]
{
    let mut left = 0;
    let mut right = sorted_vec.len();
    
    while left < right
        invariant
            left <= right,
            right <= sorted_vec.len(),
            forall|i: int| 0 <= i < left ==> sorted_vec[i] <= elem,
            forall|i: int| right <= i < sorted_vec.len() ==> elem <= sorted_vec[i]
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        if sorted_vec[mid] <= elem {
            left = mid + 1;
        } else {
            right = mid;
        }
        assert(left <= right);
        proof {
            if sorted_vec[mid] <= elem {
                assert(forall|i: int| 0 <= i < mid + 1 ==> sorted_vec[i] <= elem);
            } else {
                assert(forall|i: int| mid <= i < sorted_vec.len() ==> elem <= sorted_vec[i]);
            }
        }
    }
    left
}

fn sorted_insert(sorted_vec: &mut Vec<i32>, elem: i32)
    requires
        is_sorted(old(sorted_vec)@),
        has_no_duplicates(old(sorted_vec)@),
        !contains_element(old(sorted_vec)@, elem)
    ensures
        is_sorted(sorted_vec@),
        has_no_duplicates(sorted_vec@)
{
    let pos = find_insert_position(sorted_vec, elem);
    proof {
        lemma_sorted_insert(old(sorted_vec)@, elem, pos as int);
        lemma_no_duplicates_insert(old(sorted_vec)@, elem, pos as int);
    }
    sorted_vec.insert(pos, elem);
}

exec fn contains_element_exec(arr: &Vec<i32>, elem: i32) -> (found: bool)
    ensures
        found == contains_element(arr@, elem)
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != elem
    {
        if arr[i] == elem {
            return true;
        }
    }
    false
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
{
    /* code modified by LLM (iteration 5): simplified invariants and added proof blocks */
    let mut result = Vec::new();
    
    for k in 0..ar1.len()
        invariant
            is_sorted(result@),
            has_no_duplicates(result@)
    {
        if !contains_element_exec(ar2, ar1[k]) {
            if !contains_element_exec(&result, ar1[k]) {
                proof {
                    assert(!contains_element(result@, ar1[k]));
                }
                sorted_insert(&mut result, ar1[k]);
            }
        }
    }
    
    for k in 0..ar2.len()
        invariant
            is_sorted(result@),
            has_no_duplicates(result@)
    {
        if !contains_element_exec(ar1, ar2[k]) {
            if !contains_element_exec(&result, ar2[k]) {
                proof {
                    assert(!contains_element(result@, ar2[k]));
                }
                sorted_insert(&mut result, ar2[k]);
            }
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}