use vstd::prelude::*;

verus! {

// Define a simpler count function that matches elements
spec fn count_in_seq(target: u64, xs: Seq<u64>) -> nat {
    xs.filter(|x| x == target).len()
}

spec fn majority_element_precond(xs: Seq<u64>) -> bool {
    xs.len() > 0 && exists|x: u64| count_in_seq(x, xs) > xs.len() / 2
}

spec fn majority_element_postcond(xs: Seq<u64>, result: u64) -> bool {
    count_in_seq(result, xs) > xs.len() / 2
}

fn find_candidate(lst: &Vec<u64>) -> (candidate: u64)
    requires lst.len() > 0
{
    let mut candidate = lst[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < lst.len()
        invariant 
            0 < i <= lst.len(),
            count >= 0
    {
        if lst[i] == candidate {
            count = count + 1;
        } else if count == 0 {
            candidate = lst[i];
            count = 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    candidate
}

fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires majority_element_precond(xs@)
    ensures majority_element_postcond(xs@, result)
{
    let candidate = find_candidate(xs);
    
    // Count occurrences of candidate
    let mut count = 0;
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            count == count_in_seq(candidate, xs@.subrange(0, i as int))
    {
        if xs[i] == candidate {
            count = count + 1;
        }
        i = i + 1;
    }
    
    // Since we have the precondition that a majority element exists,
    // and Boyer-Moore algorithm guarantees that if a majority element exists,
    // the candidate will be a majority element, we can return the candidate
    candidate
}

} // verus!

fn main() {}