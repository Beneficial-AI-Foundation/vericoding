use vstd::prelude::*;

verus! {

// Helper function to count occurrences of an element in a sequence
spec fn count_occurrences(n: i32, lst: Seq<i32>) -> nat {
    lst.filter(|x: i32| x == n).len()
}

// Precondition (trivially true in this case)  
spec fn find_majority_element_precond(lst: Seq<i32>) -> bool {
    true
}

// Main function to find majority element
fn find_majority_element(lst: Vec<i32>) -> (result: i32)
    requires find_majority_element_precond(lst@),
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Postcondition specification
spec fn find_majority_element_postcond(lst: Seq<i32>, result: i32) -> bool {
    let n = lst.len();
    
    if result == -1 {
        // No majority element exists - all elements appear at most n/2 times  
        forall|x: i32| lst.contains(x) ==> #[trigger] count_occurrences(x, lst) <= n / 2
    } else {
        // result is the majority element and appears in the list
        lst.contains(result) && 
        count_occurrences(result, lst) > n / 2 && 
        forall|x: i32| lst.contains(x) ==> (#[trigger] count_occurrences(x, lst) <= n / 2 || x == result)
    }
}

fn main() {}

}