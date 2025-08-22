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
            let mut result = vec![a_first];
            let a_tail = a.subrange(1, a.len() as int);
            let merged_tail = merge_sorted_aux(a_tail, b);
            result.append(&mut merged_tail.clone());
            result
        } else {
            let mut result = vec![b_first];
            let b_tail = b.subrange(1, b.len() as int);
            let merged_tail = merge_sorted_aux(a, b_tail);
            result.append(&mut merged_tail.clone());
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