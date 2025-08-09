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
        return None;
    }
    
    let mut min = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant 
            0 < s.len(),
            1 <= i <= s.len(),
            s@.contains(min),
            forall|j: int| 0 <= j < i ==> min <= s@[j],
    {
        if s[i] < min {
            min = s[i];
        }
        i = i + 1;
    }
    
    Some(min)
}

}

fn main() {}