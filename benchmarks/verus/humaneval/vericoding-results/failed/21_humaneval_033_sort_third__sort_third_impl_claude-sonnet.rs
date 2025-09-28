// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed integer literal comparisons and sequence indexing syntax */
// Helper to check if positions divisible by 3 are sorted
fn sorted_at_third_positions(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() && i % 3 == 0int && j % 3 == 0int ==> s@[i] <= s@[j]
}

// Helper to check if non-third positions are unchanged
fn non_third_positions_unchanged(original: Seq<i8>, result: Seq<i8>) -> bool {
    forall|i: int| 0 <= i < original.len() && i % 3 != 0int ==> result@[i] == original@[i]
}

// Helper function to extract elements at positions divisible by 3
fn extract_third_positions(a: &Vec<i8>) -> (result: Vec<i8>)
    requires a@.len() > 0
    ensures result@.len() == (a@.len() + 2) / 3
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result@.len() == (i + 2) / 3,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == a@[j * 3]
    {
        if i % 3 == 0 {
            result.push(a[i]);
        }
        i += 1;
    }
    result
}

// Helper function to merge sorted third positions back
fn merge_third_positions(original: &Vec<i8>, sorted_thirds: &Vec<i8>) -> (result: Vec<i8>)
    requires
        original@.len() > 0,
        sorted_thirds@.len() == (original@.len() + 2) / 3
    ensures
        result@.len() == original@.len(),
        non_third_positions_unchanged(original@, result@),
        forall|i: int| 0 <= i < result@.len() && i % 3 == 0int ==> result@[i] == sorted_thirds@[i / 3]
{
    let mut result = Vec::new();
    let mut third_idx = 0;
    let mut i = 0;
    
    while i < original.len()
        invariant
            0 <= i <= original.len(),
            result@.len() == i,
            third_idx == (i + 2) / 3,
            forall|j: int| 0 <= j < i && j % 3 != 0int ==> result@[j] == original@[j],
            forall|j: int| 0 <= j < i && j % 3 == 0int ==> result@[j] == sorted_thirds@[j / 3]
    {
        if i % 3 == 0 {
            result.push(sorted_thirds[third_idx]);
            third_idx += 1;
        } else {
            result.push(original[i]);
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error with type mismatches */
    // Extract elements at positions divisible by 3
    let third_elements = extract_third_positions(a);
    
    // Sort the extracted elements
    let mut sorted_thirds = third_elements;
    sorted_thirds.sort();
    
    // Merge sorted elements back into original positions
    let result = merge_third_positions(a, &sorted_thirds);
    
    proof {
        // The multiset property holds because we only rearranged elements at third positions
        // and sorting preserves multisets
        assert(third_elements@.to_multiset() == sorted_thirds@.to_multiset());
    }
    
    result
}
// </vc-code>


}

fn main() {}