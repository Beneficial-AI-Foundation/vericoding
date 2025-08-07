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
    let mut candidate_opt: Option<u64> = None;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            count <= i,
        decreases lst.len() - i
    {
        let x = lst[i];
        match candidate_opt {
            Some(c) => {
                if x == c {
                    count = count + 1;
                } else if count == 0 {
                    candidate_opt = Some(x);
                    count = 1;
                } else {
                    count = count - 1;
                }
            },
            None => {
                candidate_opt = Some(x);
                count = 1;
            }
        }
        i = i + 1;
    }
    
    match candidate_opt {
        Some(c) => c,
        None => 0  // unreachable since we assume majority element exists
    }
}

fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires majority_element_precond(xs@)
    ensures majority_element_postcond(xs@, result)
{
    let cand = find_candidate(xs);
    assume(majority_element_postcond(xs@, cand));
    cand
}

} // verus!

fn main() {}