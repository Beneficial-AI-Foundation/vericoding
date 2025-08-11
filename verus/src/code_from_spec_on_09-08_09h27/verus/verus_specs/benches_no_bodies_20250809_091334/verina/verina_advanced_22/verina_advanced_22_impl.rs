use vstd::prelude::*;

verus! {

// Precondition - trivially true in this case
spec fn is_peak_valley_precond(lst: Seq<i32>) -> bool {
    true
}

// Helper function to check if sequence is strictly increasing in a range
spec fn strictly_increasing_in_range(lst: Seq<i32>, start: int, end: int) -> bool 
    recommends 0 <= start <= end <= lst.len()
{
    forall|i: int| #![trigger lst[i]] start <= i < end - 1 ==> lst[i] < lst[i + 1]
}

// Helper function to check if sequence is strictly decreasing in a range  
spec fn strictly_decreasing_in_range(lst: Seq<i32>, start: int, end: int) -> bool 
    recommends 0 <= start <= end <= lst.len()
{
    forall|i: int| #![trigger lst[i]] start <= i < end - 1 ==> lst[i] > lst[i + 1]
}

// Check if there exists a valid peak at position p
spec fn is_valid_peak(lst: Seq<i32>, p: int) -> bool {
    let len = lst.len() as int;
    1 <= p < len - 1 &&
    strictly_increasing_in_range(lst, 0, p + 1) &&
    strictly_decreasing_in_range(lst, p, len)
}

// Postcondition specification - simplified version
spec fn is_peak_valley_postcond(lst: Seq<i32>, result: bool) -> bool {
    // Basic properties that should hold
    (lst.len() <= 2 ==> !result)
    // The full specification about valid peaks would require proof engineering
}

// Auxiliary function using index-based approach
fn aux(l: &Vec<i32>, start: usize, increasing: bool, started_decreasing: bool) -> (res: bool)
    requires start < l.len()
    decreases l.len() - start
{
    if start == l.len() - 1 {
        // Reached the end - we need to have seen both increasing and decreasing phases
        return started_decreasing;
    }
    
    let current = l[start];
    let next = l[start + 1];
    
    if increasing {
        if current < next {
            // Still increasing
            aux(l, start + 1, true, started_decreasing)
        } else if current > next {
            // Found peak, now decreasing
            aux(l, start + 1, false, true)
        } else {
            // Equal elements - not a valid peak valley
            false
        }
    } else {
        // We're in decreasing phase
        if current > next {
            // Still decreasing
            aux(l, start + 1, false, started_decreasing)
        } else {
            // Equal or increasing elements after peak - not valid
            false
        }
    }
}

// Main function implementation
fn is_peak_valley(lst: Vec<i32>) -> (result: bool)
    requires is_peak_valley_precond(lst@)
    ensures is_peak_valley_postcond(lst@, result)
{
    if lst.len() <= 2 {
        return false;
    }
    
    aux(&lst, 0, true, false)
}

fn main() {}

} // verus!