// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors with proper nat/int conversions and sequence indexing */
fn merge_sorted_spec(arr1: Seq<int>, arr2: Seq<int>) -> (result: Seq<int>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len()
{
    if arr1.len() == 0 {
        arr2
    } else if arr2.len() == 0 {
        arr1
    } else if arr1[0] <= arr2[0] {
        seq![arr1[0]].add(merge_sorted_spec(arr1.subrange(1 as int, arr1.len() as int), arr2))
    } else {
        seq![arr2[0]].add(merge_sorted_spec(arr1, arr2.subrange(1 as int, arr2.len() as int)))
    }
}

proof fn merge_sorted_lemma(arr1: Seq<int>, arr2: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < merge_sorted_spec(arr1, arr2).len() ==> 
            merge_sorted_spec(arr1, arr2)[i] <= merge_sorted_spec(arr1, arr2)[j],
        merge_sorted_spec(arr1, arr2).len() == arr1.len() + arr2.len()
{
    if arr1.len() == 0 {
        assert(arr2.len() == merge_sorted_spec(arr1, arr2).len());
    } else if arr2.len() == 0 {
        assert(arr1.len() == merge_sorted_spec(arr1, arr2).len());
    } else if arr1[0] <= arr2[0] {
        let sub_seq = merge_sorted_spec(arr1.subrange(1 as int, arr1.len() as int), arr2);
        assert forall|i: int, j: int| 0 <= i < j < sub_seq.len() implies sub_seq[i] <= sub_seq[j] by {
            merge_sorted_lemma(arr1.subrange(1 as int, arr1.len() as int), arr2);
        };
    } else {
        let sub_seq = merge_sorted_spec(arr1, arr2.subrange(1 as int, arr2.len() as int));
        assert forall|i: int, j: int| 0 <= i < j < sub_seq.len() implies sub_seq[i] <= sub_seq[j] by {
            merge_sorted_lemma(arr1, arr2.subrange(1 as int, arr2.len() as int));
        };
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
/* code modified by LLM (iteration 5): Fixed compilation errors with proper sequence conversion */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < arr1.len() && j < arr2.len()
        invariant
            0 <= i <= arr1.len(),
            0 <= j <= arr2.len(),
            result.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] <= result[l]
    {
        if arr1[i] <= arr2[j] {
            result.push(arr1[i]);
            i += 1;
        } else {
            result.push(arr2[j]);
            j += 1;
        }
    }
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            result.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] <= result[l]
    {
        result.push(arr1[i]);
        i += 1;
    }
    
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            result.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] <= result[l]
    {
        result.push(arr2[j]);
        j += 1;
    }
    
    proof {
        merge_sorted_lemma(arr1@.map(|x: i32| x as int), arr2@.map(|x: i32| x as int));
    }
    
    result
}
// </vc-code>

}
fn main() {}