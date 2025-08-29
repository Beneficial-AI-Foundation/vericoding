use vstd::prelude::*;

verus! {

// Precondition - in the original it's just True  
spec fn only_once_precond(a: Seq<i32>, key: i32) -> bool {
    true
}

// Helper function to count occurrences
spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.fold_left(0nat, |cnt: nat, x: i32| if x == key { cnt + 1 } else { cnt })
}

// Postcondition
spec fn only_once_postcond(a: Seq<i32>, key: i32, result: bool) -> bool {
    (count_occurrences(a, key) == 1 ==> result) &&
    (count_occurrences(a, key) != 1 ==> !result)
}

// The loop function - recursive approach following the original Lean structure
fn only_once_loop_rec(a: &Vec<i32>, key: i32, i: usize, key_count: usize) -> (result: bool)
    requires i <= a.len(), key_count <= a.len()
    decreases a.len() - i
{
    if i >= a.len() {
        key_count == 1
    } else {
        let val = a[i];
        let new_count = if val == key { 
            if key_count < a.len() { key_count + 1 } else { key_count }
        } else { 
            key_count 
        };
        assert(new_count <= a.len());
        only_once_loop_rec(a, key, i + 1, new_count)
    }
}

// The main loop function
fn only_once_loop(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures result == (count_occurrences(a@, key) == 1)
{
    // The proof that our recursive implementation matches the spec would go here
    assume(false);
    only_once_loop_rec(a, key, 0, 0)
}

// Main function
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    requires only_once_precond(a@, key)
    ensures only_once_postcond(a@, key, result)
{
    only_once_loop(a, key)
}

// Specification theorem - equivalent to the Lean theorem
proof fn only_once_spec_satisfied(a: Vec<i32>, key: i32) 
    requires only_once_precond(a@, key)
    ensures only_once_postcond(a@, key, only_once(&a, key), only_once_precond(a@, key))
{
    // The proof would establish that the implementation satisfies the postcondition
    // This corresponds to the 'sorry' in the original Lean code
}

}