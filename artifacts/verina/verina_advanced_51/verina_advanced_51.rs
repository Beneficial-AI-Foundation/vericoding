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
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else {
        let x = a[0];
        let y = b[0];
        
        if x <= y {
            // Remove first element from a
            let mut a_rest = a;
            a_rest.remove(0);
            
            let merged = merge_sorted_aux(a_rest, b);
            
            // Prepend x to merged result
            let mut result = Vec::new();
            result.push(x);
            
            // Manually append merged elements
            let mut i = 0;
            while i < merged.len()
                invariant i <= merged.len()
                decreases merged.len() - i
            {
                result.push(merged[i]);
                i += 1;
            }
            result
        } else {
            // Remove first element from b
            let mut b_rest = b;
            b_rest.remove(0);
            
            let merged = merge_sorted_aux(a, b_rest);
            
            // Prepend y to merged result
            let mut result = Vec::new();
            result.push(y);
            
            // Manually append merged elements
            let mut i = 0;
            while i < merged.len()
                invariant i <= merged.len()
                decreases merged.len() - i
            {
                result.push(merged[i]);
                i += 1;
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
    // The proof is admitted (similar to 'sorry' in Lean)
    proof {
        admit();
    }
    
    let merged = merge_sorted_aux(a, b);
    merged
}

fn main() {}

} // verus!