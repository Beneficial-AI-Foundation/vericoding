use vstd::prelude::*;

verus! {

// Precondition: array must be non-empty (matching Lean's a.size > 0)
spec fn difference_min_max_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Helper to compute fold-based minimum using accumulator pattern like Lean's foldl
spec fn fold_min_helper(a: &Vec<i32>, start_idx: nat, current_min: i32) -> i32
    decreases a.len() - start_idx
{
    if start_idx >= a.len() {
        current_min
    } else {
        let x = a[start_idx as int];
        let new_min = if x < current_min { x } else { current_min };
        fold_min_helper(a, start_idx + 1, new_min)
    }
}

// Helper to compute fold-based maximum using accumulator pattern like Lean's foldl
spec fn fold_max_helper(a: &Vec<i32>, start_idx: nat, current_max: i32) -> i32
    decreases a.len() - start_idx
{
    if start_idx >= a.len() {
        current_max
    } else {
        let x = a[start_idx as int];
        let new_max = if x > current_max { x } else { current_max };
        fold_max_helper(a, start_idx + 1, new_max)
    }
}

// Fold-style min computation (matching Lean's a.foldl with a[0]! as initial)
spec fn fold_min(a: &Vec<i32>) -> i32 {
    fold_min_helper(a, 1, a[0])
}

// Fold-style max computation (matching Lean's a.foldl with a[0]! as initial)
spec fn fold_max(a: &Vec<i32>) -> i32 {
    fold_max_helper(a, 1, a[0])
}

// Postcondition: result + min = max (directly matching Lean's postcondition)
spec fn difference_min_max_postcond(a: &Vec<i32>, result: i32) -> bool {
    result + fold_min(a) == fold_max(a)
}

fn difference_min_max(a: &Vec<i32>) -> (result: i32)
    requires difference_min_max_precond(a)
    ensures difference_min_max_postcond(a, result)
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    
    let mut i = 1;
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            min_val == fold_min_helper(a, i, a[0]),
            max_val == fold_max_helper(a, i, a[0])
    {
        /* code modified by LLM (iteration 1): fix type error by using usize indexing instead of int */
        if a[i] < min_val {
            min_val = a[i];
        }
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    
    max_val - min_val
}

// Theorem corresponding to Lean's differenceMinMax_spec_satisfied
proof fn difference_min_max_spec_satisfied(a: &Vec<i32>)
    requires difference_min_max_precond(a)
    ensures difference_min_max_postcond(a, difference_min_max(a))
{
    // The proof follows directly from the ensures clause of difference_min_max
}

fn main() {}

}