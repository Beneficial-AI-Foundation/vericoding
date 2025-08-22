use vstd::prelude::*;

verus! {

// Precondition: array must have positive size
spec fn has_only_one_distinct_element_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Helper function to check if all elements in a slice are equal to a given value
spec fn all_equal_to(a: &Vec<i32>, value: i32) -> bool {
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == value
}

// Helper function to check if there exists an element different from the first
spec fn exists_different_from_first(a: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[i as int][0]
}

// Postcondition
spec fn has_only_one_distinct_element_postcond(a: &Vec<i32>, result: bool) -> bool {
    (result ==> all_equal_to(a, a[0])) &&
    (!result ==> exists_different_from_first(a))
}

fn has_only_one_distinct_element(a: &Vec<i32>) -> (result: bool)
    requires has_only_one_distinct_element_precond(a)
    ensures has_only_one_distinct_element_postcond(a, result)
{
    let first_element = a[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] == first_element
        decreases a.len() - i
    {
        if a[i] != first_element {
            /* code modified by LLM (iteration 1): added proof block to establish postcondition for early return */
            proof {
                assert(a[i as int] != first_element);
                assert(0 <= i < a.len());
                assert(exists|k: int| 0 <= k < a.len() && a[k] != a[0]);
            }
            return false;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added proof block to establish postcondition for true case */
    proof {
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] == first_element);
        assert(all_equal_to(a, a[0]));
    }
    true
}

fn main() {}

} // verus!