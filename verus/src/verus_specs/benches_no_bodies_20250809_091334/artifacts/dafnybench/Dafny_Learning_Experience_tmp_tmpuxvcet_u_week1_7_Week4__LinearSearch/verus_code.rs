use vstd::prelude::*;

verus! {
    // First version of linear search - finds first element equal to target
    fn linear_search0(a: &Vec<u32>, target: u32) -> (n: usize)
        requires true,
        ensures 
            n <= a.len(),
            n < a.len() ==> a[n as int] == target,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Enhanced version with stronger postcondition  
    fn linear_search1(a: &Vec<u32>, target: u32) -> (n: usize)
        requires true,
        ensures 
            n <= a.len(),
            n < a.len() ==> a[n as int] == target,
            n == a.len() ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != target),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Test function
    fn test_linear_search() {
    // TODO: Remove this comment and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}