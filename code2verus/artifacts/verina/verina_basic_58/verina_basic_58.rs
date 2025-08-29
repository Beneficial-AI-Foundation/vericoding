use vstd::prelude::*;

verus! {

// Precondition for double_array_elements
spec fn double_array_elements_precond(s: Vec<i32>) -> bool {
    // Need to ensure no overflow when doubling
    forall|i: int| #![auto] 0 <= i < s.len() ==> s[i] <= i32::MAX / 2 && s[i] >= i32::MIN / 2
}

// Postcondition for double_array_elements
spec fn double_array_elements_postcond(s: Vec<i32>, result: Vec<i32>) -> bool {
    result.len() == s.len() &&
    forall|i: int| #![auto] 0 <= i < s.len() ==> result[i] == 2 * s[i]
}

// Auxiliary recursive function with stronger specification
fn double_array_elements_aux(s_old: Vec<i32>, s: Vec<i32>, i: usize) -> (result: Vec<i32>)
    requires
        s.len() == s_old.len(),
        i <= s.len(),
        double_array_elements_precond(s_old),
        // Elements up to i have been doubled
        forall|j: int| #![auto] 0 <= j < i ==> s[j] == 2 * s_old[j],
        // Elements from i onward are unchanged
        forall|j: int| #![auto] i <= j < s.len() ==> s[j] == s_old[j],
    ensures
        result.len() == s.len(),
        forall|j: int| #![auto] 0 <= j < s.len() ==> result[j] == 2 * s_old[j],
    decreases s.len() - i
{
    if i < s.len() {
        let mut new_s = s;
        new_s.set(i, 2 * s_old[i]);
        double_array_elements_aux(s_old, new_s, i + 1)
    } else {
        s
    }
}

// Main function
fn double_array_elements(s: Vec<i32>) -> (result: Vec<i32>)
    requires
        double_array_elements_precond(s),
    ensures
        double_array_elements_postcond(s, result),
{
    double_array_elements_aux(s.clone(), s, 0)
}

}

fn main() {}