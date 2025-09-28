// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified spec function and added element containment lemma */
spec fn merge_sorted_lists_spec(arr1: Seq<i32>, arr2: Seq<i32>, i1: int, i2: int) -> Seq<i32>
    decreases arr1.len() - i1 + arr2.len() - i2
{
    if i1 >= arr1.len() && i2 >= arr2.len() {
        Seq::empty()
    } else if i1 >= arr1.len() {
        seq![arr2[i2]] + merge_sorted_lists_spec(arr1, arr2, i1, i2 + 1)
    } else if i2 >= arr2.len() {
        seq![arr1[i1]] + merge_sorted_lists_spec(arr1, arr2, i1 + 1, i2)
    } else if arr1[i1] <= arr2[i2] {
        seq![arr1[i1]] + merge_sorted_lists_spec(arr1, arr2, i1 + 1, i2)
    } else {
        seq![arr2[i2]] + merge_sorted_lists_spec(arr1, arr2, i1, i2 + 1)
    }
}

proof fn lemma_merge_sorted_lists_sorted(arr1: Seq<i32>, arr2: Seq<i32>, i1: int, i2: int)
    requires
        0 <= i1 <= arr1.len(),
        0 <= i2 <= arr2.len(),
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < merge_sorted_lists_spec(arr1, arr2, i1, i2).len() ==> 
            merge_sorted_lists_spec(arr1, arr2, i1, i2)[i] <= merge_sorted_lists_spec(arr1, arr2, i1, i2)[j],
    decreases arr1.len() - i1 + arr2.len() - i2
{
    let merged = merge_sorted_lists_spec(arr1, arr2, i1, i2);
    if i1 >= arr1.len() && i2 >= arr2.len() {
    } else if i1 >= arr1.len() {
        if i2 + 1 < arr2.len() {
            lemma_merge_sorted_lists_sorted(arr1, arr2, i1, i2 + 1);
        }
    } else if i2 >= arr2.len() {
        if i1 + 1 < arr1.len() {
            lemma_merge_sorted_lists_sorted(arr1, arr2, i1 + 1, i2);
        }
    } else if arr1[i1] <= arr2[i2] {
        lemma_merge_sorted_lists_sorted(arr1, arr2, i1 + 1, i2);
    } else {
        lemma_merge_sorted_lists_sorted(arr1, arr2, i1, i2 + 1);
    }
}

proof fn lemma_merge_length(arr1: Seq<i32>, arr2: Seq<i32>, i1: int, i2: int)
    requires
        0 <= i1 <= arr1.len(),
        0 <= i2 <= arr2.len(),
    ensures
        merge_sorted_lists_spec(arr1, arr2, i1, i2).len() == (arr1.len() - i1) + (arr2.len() - i2),
    decreases arr1.len() - i1 + arr2.len() - i2
{
    if i1 >= arr1.len() && i2 >= arr2.len() {
    } else if i1 >= arr1.len() {
        lemma_merge_length(arr1, arr2, i1, i2 + 1);
    } else if i2 >= arr2.len() {
        lemma_merge_length(arr1, arr2, i1 + 1, i2);
    } else if arr1[i1] <= arr2[i2] {
        lemma_merge_length(arr1, arr2, i1 + 1, i2);
    } else {
        lemma_merge_length(arr1, arr2, i1, i2 + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed problematic trigger annotations from invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    while i1 < arr1.len() || i2 < arr2.len()
        invariant
            0 <= i1 <= arr1.len(),
            0 <= i2 <= arr2.len(),
            result.len() == i1 + i2,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
            result@ == merge_sorted_lists_spec(arr1@, arr2@, 0, 0).take(i1 as int + i2 as int),
        decreases arr1.len() + arr2.len() - i1 - i2
    {
        if i1 >= arr1.len() {
            result.push(arr2[i2]);
            i2 = i2 + 1;
        } else if i2 >= arr2.len() {
            result.push(arr1[i1]);
            i1 = i1 + 1;
        } else if arr1[i1] <= arr2[i2] {
            result.push(arr1[i1]);
            i1 = i1 + 1;
        } else {
            result.push(arr2[i2]);
            i2 = i2 + 1;
        }
        
        proof {
            lemma_merge_sorted_lists_sorted(arr1@, arr2@, 0, 0);
            assert(result@.len() == i1 + i2);
        }
    }
    
    proof {
        assert(i1 == arr1.len());
        assert(i2 == arr2.len());
        lemma_merge_length(arr1@, arr2@, 0, 0);
        assert(result.len() == arr1.len() + arr2.len());
        lemma_merge_sorted_lists_sorted(arr1@, arr2@, 0, 0);
    }
    
    result
}
// </vc-code>

}
fn main() {}