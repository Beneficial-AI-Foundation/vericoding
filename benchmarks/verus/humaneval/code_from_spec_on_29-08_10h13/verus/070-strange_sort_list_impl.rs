use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
fn min_max_indices(v: &Vec<i32>) -> (result: (usize, usize))
    requires v.len() > 0
    ensures 
        result.0 < v.len() && result.1 < v.len(),
        #[trigger] forall|i: int| 0 <= i < v.len() ==> v@[result.0 as int] <= v@[i],
        #[trigger] forall|i: int| 0 <= i < v.len() ==> v@[i] <= v@[result.1 as int]
{
    let mut min_idx = 0;
    let mut max_idx = 0;
    let mut i = 1;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            min_idx < v.len(),
            max_idx < v.len(),
            forall|j: int| 0 <= j < i ==> v@[min_idx as int] <= v@[j],
            forall|j: int| 0 <= j < i ==> v@[j] <= v@[max_idx as int]
        decreases v.len() - i
    {
        if v[i] < v[min_idx] {
            min_idx = i;
        }
        if v[i] > v[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    (min_idx, max_idx)
}

proof fn lemma_remove_preserves_multiset(v_before: Seq<i32>, v_after: Seq<i32>, removed: i32)
    requires v_before.len() == v_after.len() + 1,
             exists|i: int| 0 <= i < v_before.len() && v_before[i] == removed && v_after == v_before.remove(i),
    ensures v_before.to_multiset() == v_after.to_multiset().insert(removed)
{}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def strange_sort_list(lst: List[int]) -> List[int]"
docstring: |
Given list of integers, return list in strange order.
Strange sorting is when you start with the minimum value,
then the maximum of the remaining integers, then the minimum and so on.
test_cases:
- input: [1, 2, 3, 4]
expected_output: [1, 4, 2, 3]
- input: [5, 5, 5, 5]
expected_output: [5, 5, 5, 5]
- input: []
expected_output: []
*/
// </vc-description>

// <vc-spec>
fn strange_sort_list(lst: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == lst.len(),
        result@.to_multiset() == lst@.to_multiset()
// </vc-spec>

// <vc-code>
{
    let mut remaining = lst;
    let mut result = Vec::new();
    let mut take_min = true;
    
    while remaining.len() > 0
        invariant
            result.len() + remaining.len() == lst.len(),
            /* code modified by LLM (iteration 5): fixed union to add, captured old state properly */
            result@.to_multiset().add(remaining@.to_multiset()) == lst@.to_multiset()
        decreases remaining.len()
    {
        let (min_idx, max_idx) = min_max_indices(&remaining);
        let idx_to_remove = if take_min { min_idx } else { max_idx };
        let value = remaining[idx_to_remove];
        /* code modified by LLM (iteration 5): captured old remaining state before modifications */
        let ghost old_remaining = remaining@;
        result.push(value);
        remaining.remove(idx_to_remove);
        take_min = !take_min;
        
        proof {
            /* code modified by LLM (iteration 5): used ghost variable for old state */
            lemma_remove_preserves_multiset(old_remaining, remaining@, value);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}