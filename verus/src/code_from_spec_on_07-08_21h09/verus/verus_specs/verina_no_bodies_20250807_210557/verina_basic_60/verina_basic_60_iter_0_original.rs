use vstd::prelude::*;

verus! {

// Helper function to check if a number is even
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

fn is_even_exec(n: i32) -> (result: bool)
    ensures result == is_even(n as int)
{
    return false;  // TODO: Remove this line and implement the function body
}

// Precondition - always true  
spec fn find_even_numbers_precond(arr: Seq<i32>) -> bool {
    true
}

// Postcondition with both properties
spec fn find_even_numbers_postcond(arr: Seq<i32>, result: Seq<i32>) -> bool {
    // All elements in result are even and exist in arr
    forall|j: int| 0 <= j < result.len() ==> {
        &&& #[trigger] is_even(result[j] as int) 
        &&& exists|k: int| 0 <= k < arr.len() && arr[k] == result[j]
    }
}

// Main function to find even numbers
fn find_even_numbers(arr: Vec<i32>) -> (result: Vec<i32>)
    requires find_even_numbers_precond(arr@)  
    ensures find_even_numbers_postcond(arr@, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}