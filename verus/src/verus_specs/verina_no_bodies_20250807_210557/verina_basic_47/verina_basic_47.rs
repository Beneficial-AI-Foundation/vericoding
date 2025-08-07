use vstd::prelude::*;

verus! {

// Precondition: array must have size > 0
spec fn array_sum_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Helper function to compute sum up to index n (matches Lean's sumTo)
spec fn sum_to(a: &Vec<i32>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0int
    } else {
        sum_to(a, (n - 1) as nat) + a[(n - 1) as int] as int  
    }
}

// Postcondition specification (matches Lean's arraySum_postcond)
spec fn array_sum_postcond(a: &Vec<i32>, result: i32) -> bool {
    &&& result as int - sum_to(a, a.len() as nat) == 0
    &&& result as int >= sum_to(a, a.len() as nat)  
}

// Main function (direct translation of Lean's arraySum)
#[verifier::exec_allows_no_decreases_clause]  
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires array_sum_precond(a)
    ensures array_sum_postcond(a, result)
{
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}