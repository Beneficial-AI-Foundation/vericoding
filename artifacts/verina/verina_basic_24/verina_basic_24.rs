use vstd::prelude::*;

verus! {

// Helper functions for even/odd checking  
spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}

// Precondition specification
spec fn first_even_odd_difference_precond(a: Seq<i32>) -> bool {
    &&& a.len() > 1
    &&& exists|i: int| 0 <= i < a.len() && is_even(a[i])
    &&& exists|i: int| 0 <= i < a.len() && is_odd(a[i])
}

// Postcondition specification
spec fn first_even_odd_difference_postcond(a: Seq<i32>, result: i32) -> bool {
    exists|i: int, j: int| {
        &&& 0 <= i < a.len()
        &&& 0 <= j < a.len()
        &&& is_even(a[i])
        &&& is_odd(a[j])
        &&& result == a[i] - a[j]
        &&& forall|k: int| #![auto] 0 <= k < i ==> is_odd(a[k])
        &&& forall|k: int| #![auto] 0 <= k < j ==> is_even(a[k])
    }
}

// Function to find first even index
fn find_first_even(a: &Vec<i32>) -> (result: Option<usize>)
    ensures 
        result.is_some() ==> {
            let idx = result.unwrap() as int;
            &&& 0 <= idx < a.len()
            &&& is_even(a@[idx])
            &&& forall|k: int| #![auto] 0 <= k < idx ==> is_odd(a@[k])
        },
        result.is_none() ==> forall|k: int| #![auto] 0 <= k < a.len() ==> is_odd(a@[k]),
{
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < i ==> is_odd(a@[k]),
    {
        if a[i] % 2 == 0 {
            return Some(i);
        }
    }
    None
}

// Function to find first odd index
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    ensures 
        result.is_some() ==> {
            let idx = result.unwrap() as int;
            &&& 0 <= idx < a.len()
            &&& is_odd(a@[idx])
            &&& forall|k: int| #![auto] 0 <= k < idx ==> is_even(a@[k])
        },
        result.is_none() ==> forall|k: int| #![auto] 0 <= k < a.len() ==> is_even(a@[k]),
{
    for i in 0..a.len()
        invariant
            forall|k: int| #![auto] 0 <= k < i ==> is_even(a@[k]),
    {
        if a[i] % 2 != 0 {
            return Some(i);
        }
    }
    None
}

// Main function implementation  
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        first_even_odd_difference_precond(a@),
        // Additional bounds to prevent overflow
        forall|i: int| #![trigger a@[i]] 0 <= i < a.len() ==> -1000000000 <= a@[i] <= 1000000000,
    ensures
        first_even_odd_difference_postcond(a@, result),
{
    let first_even_idx = find_first_even(a);
    let first_odd_idx = find_first_odd(a);
    
    proof {
        // From the precondition, we know both even and odd elements exist
        assert(exists|i: int| 0 <= i < a.len() && is_even(a@[i]));
        assert(exists|i: int| 0 <= i < a.len() && is_odd(a@[i]));
    }
    
    let even_idx = first_even_idx.unwrap();
    let odd_idx = first_odd_idx.unwrap();
    
    let even_val = a[even_idx];
    let odd_val = a[odd_idx];
    let result = even_val - odd_val;
    
    proof {
        let i = even_idx as int;
        let j = odd_idx as int;
        
        assert(0 <= i < a.len());
        assert(0 <= j < a.len());
        assert(is_even(a@[i]));
        assert(is_odd(a@[j]));
        assert(even_val == a@[i]);
        assert(odd_val == a@[j]);
        assert(result == a@[i] - a@[j]);
        assert(forall|k: int| #![auto] 0 <= k < i ==> is_odd(a@[k]));
        assert(forall|k: int| #![auto] 0 <= k < j ==> is_even(a@[k]));
        
        // Establish the postcondition
        assert(first_even_odd_difference_postcond(a@, result)) by {
            assert(exists|i: int, j: int| {
                &&& 0 <= i < a.len()
                &&& 0 <= j < a.len()
                &&& is_even(a@[i])
                &&& is_odd(a@[j])
                &&& result == a@[i] - a@[j]
                &&& forall|k: int| #![auto] 0 <= k < i ==> is_odd(a@[k])
                &&& forall|k: int| #![auto] 0 <= k < j ==> is_even(a@[k])
            });
        }
    }
    
    result
}

fn main() {}

} // verus!