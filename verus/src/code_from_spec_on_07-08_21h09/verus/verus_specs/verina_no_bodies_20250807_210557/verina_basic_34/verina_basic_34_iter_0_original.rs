use vstd::prelude::*;

verus! {

// Helper function to check if a number is even
spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

// Precondition for findEvenNumbers  
spec fn find_even_numbers_precond(arr: Seq<i32>) -> bool {
    true
}

// Postcondition for findEvenNumbers
spec fn find_even_numbers_postcond(arr: Seq<i32>, result: Seq<i32>) -> bool {
    // All elements in result are even and from original array
    (forall|x: i32| result.contains(x) ==> is_even(x) && arr.contains(x)) &&
    // All even elements from original array are in result  
    (forall|x: i32| arr.contains(x) && is_even(x) ==> result.contains(x))
}

// Main function
fn find_even_numbers(arr: Vec<i32>) -> (result: Vec<i32>)
    requires find_even_numbers_precond(arr@)
    ensures find_even_numbers_postcond(arr@, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!