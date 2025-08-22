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
    if i >= j {
        return true;
    }
    
    if x[i] != x[j] {
        return false;
    }
    
    is_palindrome_helper(x, i + 1, j - 1)
}

// Main IsPalindrome function - using assume to match the Lean "sorry"
fn is_palindrome(x: &Vec<char>) -> (result: bool)
    requires
        is_palindrome_precond(x@),
    ensures
        is_palindrome_postcond(x@, result),
{
    if x.len() == 0 {
        return true;
    }
    
    let mut i = 0;
    let mut j = x.len() - 1;
    
    /* code modified by LLM (iteration 1): Fixed trigger annotations to avoid arithmetic/non-arithmetic conflict */
    while i < j
        invariant
            i <= j,
            i < x.len(),
            j < x.len(),
            forall|k: int| 0 <= k < i ==> x@[k] == #[trigger] x@[(x@.len() - 1 - k) as int],
            forall|k: int| (j as int) < k < x@.len() ==> x@[k] == #[trigger] x@[(x@.len() - 1 - k) as int],
        decreases j - i
    {
        if x[i] != x[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }
    
    true
}

}

fn main() {}