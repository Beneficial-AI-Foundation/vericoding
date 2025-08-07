use vstd::prelude::*;

verus! {

// Precondition for findSmallest
spec fn find_smallest_precond(s: Seq<u32>) -> bool {
    true
}

// Postcondition for findSmallest
spec fn find_smallest_postcond(s: Seq<u32>, result: Option<u32>) -> bool {
    match result {
        None => s.len() == 0,
        Some(r) => s.contains(r) && (forall|x: u32| s.contains(x) ==> r <= x)
    }
}

// Find the smallest element in a sequence
fn find_smallest(s: &Vec<u32>) -> (result: Option<u32>)
    requires find_smallest_precond(s@),
    ensures find_smallest_postcond(s@, result),
{
    if s.len() == 0 {
        None
    } else {
        let mut min_val = s[0];
        let mut min_idx = 0;
        
        for i in 1..s.len()
            invariant 
                0 < s.len(),
                0 <= min_idx < s.len(),
                min_val == s[min_idx as int],
                forall|j: int| 0 <= j < i ==> min_val <= x[j],
        {
            if s[i] < min_val {
                min_val = s[i];
                min_idx = i;
            }
        }
        
        assert(s@.contains(min_val));
        assert(forall|x: u32| s@.contains(x) ==> min_val <= x);
        
        Some(min_val)
    }
}

}

fn main() {}