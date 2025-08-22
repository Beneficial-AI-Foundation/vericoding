use vstd::prelude::*;

verus! {

// Predicate to check if a sequence is sorted (pairwise ordering)
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Precondition: both input lists are sorted
spec fn merge_sorted_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    is_sorted(a) && is_sorted(b)
}

// Postcondition: result is sorted and is a permutation of concatenated inputs
spec fn merge_sorted_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    is_sorted(result) && result =~= a + b
}

// Auxiliary recursive merge function - structure matches original Lean code
fn merge_sorted_aux(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(a@) && is_sorted(b@),
    ensures
        is_sorted(result@) && result@ =~= a@ + b@,
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else {
        let a_first = a[0];
        let b_first = b[0];
        
        if a_first <= b_first {
            /* code modified by LLM (iteration 2): Fixed int cast issue by using usize for slice bounds */
            let a_tail = a.slice(1, a.len());
            let merged_tail = merge_sorted_aux(a_tail, b);
            let mut result = Vec::new();
            result.push(a_first);
            for i in 0..merged_tail.len()
                invariant
                    result.len() == i + 1,
                    result@[0] == a_first,
                    result@.subrange(1, result.len() as int) =~= merged_tail@.subrange(0, i as int),
            {
                result.push(merged_tail[i]);
            }
            result
        } else {
            /* code modified by LLM (iteration 2): Fixed int cast issue by using usize for slice bounds */
            let b_tail = b.slice(1, b.len());
            let merged_tail = merge_sorted_aux(a, b_tail);
            let mut result = Vec::new();
            result.push(b_first);
            for i in 0..merged_tail.len()
                invariant
                    result.len() == i + 1,
                    result@[0] == b_first,
                    result@.subrange(1, result.len() as int) =~= merged_tail@.subrange(0, i as int),
            {
                result.push(merged_tail[i]);
            }
            result
        }
    }
}

// Main merge function
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires
        merge_sorted_precond(a@, b@),
    ensures
        merge_sorted_postcond(a@, b@, result@),
{
    merge_sorted_aux(a, b)
}

fn main() {}

} // verus!