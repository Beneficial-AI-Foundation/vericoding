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
    ensures
        result == (forall|k: int| i <= k <= j ==> 
            #[trigger] x@[k] == x@[(i + j) as int - k])
    decreases j - i
{
    if i >= j {
        true
    } else if x[i] != x[j] {
        false
    } else {
        is_palindrome_helper(x, i + 1, j - 1)
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
        /* code modified by LLM (iteration 1): Added trigger annotations and proper proof structure */
        let helper_result = is_palindrome_helper(x, 0, x.len() - 1);
        
        proof {
            // Prove that the helper function result implies the postcondition
            if helper_result {
                assert(forall|i: int| 0 <= i < x@.len() ==> 
                    #[trigger] x@[i] == x@[(x@.len() - 1 - i) as int]) by {
                    // The helper ensures that for all k in range [0, len-1],
                    // x[k] == x[(0 + len-1) - k] = x[len-1-k]
                    assert(forall|k: int| 0 <= k <= (x@.len() - 1) as int ==> 
                        #[trigger] x@[k] == x@[(0 + (x@.len() - 1) as int) - k]);
                };
            } else {
                assert(exists|i: int| 0 <= i < x@.len() && 
                    #[trigger] x@[i] != x@[(x@.len() - 1 - i) as int]) by {
                    // If helper returns false, there exists some mismatch
                    assert(!forall|k: int| 0 <= k <= (x@.len() - 1) as int ==> 
                        x@[k] == x@[(0 + (x@.len() - 1) as int) - k]);
                };
            }
        }
        
        helper_result
    }
}

}

fn main() {}