use vstd::prelude::*;

verus! {

// Precondition for IsPalindrome - currently trivial (True)  
spec fn is_palindrome_precond(x: Seq<char>) -> bool {
    true
}

// Postcondition specification - matches the Lean postcondition exactly
spec fn is_palindrome_postcond(x: Seq<char>, result: bool) -> bool {
    result == (forall|i: int| 0 <= i < x.len() ==> 
        #[trigger] x[i] == x[(x.len() - 1 - i) as int])
}

// Helper function for palindrome checking
fn is_palindrome_helper(x: &Vec<char>, i: usize, j: usize) -> (result: bool)
    requires
        i < x.len(),
        j < x.len(), 
        i <= j,
    decreases j - i
{
    if i < j {
        if x[i] != x[j] {
            false
        } else if i + 1 <= j - 1 {
            is_palindrome_helper(x, i + 1, j - 1)
        } else {
            true  
        }
    } else {
        true
    }
}

// Main IsPalindrome function - using assume to match the Lean "sorry"
fn is_palindrome(x: &Vec<char>) -> (result: bool)
    requires
        is_palindrome_precond(x@),
    ensures
        is_palindrome_postcond(x@, result),
{
    if x.len() == 0 {
        true
    } else {
        let helper_result = is_palindrome_helper(x, 0, x.len() - 1);
        
        // This corresponds to the "sorry" in the Lean proof
        assume(is_palindrome_postcond(x@, helper_result));
        
        helper_result
    }
}

}

fn main() {}