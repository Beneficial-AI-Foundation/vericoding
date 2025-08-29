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
    exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[0]
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
    if a.len() == 0 {
        true
    } else {
        let first_element = a[0];
        let mut i: usize = 1;
        
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == first_element,
                first_element == a[0]
            decreases a.len() - i
        {
            if a[i] != first_element {
                // Assert that we found an element different from the first
                assert(a[i as int] != a[0]);
                assert(exists_different_from_first(a));
                return false;
            }
            i += 1;
        }
        true
    }
}

fn main() {}

} // verus!