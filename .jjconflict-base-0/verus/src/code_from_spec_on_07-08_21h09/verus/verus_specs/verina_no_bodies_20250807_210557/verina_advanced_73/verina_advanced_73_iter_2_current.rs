use vstd::prelude::*;

verus! {

spec fn is_sorted(l: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j]
}

spec fn smallest_missing_precond(l: Seq<usize>) -> bool {
    is_sorted(l)
}

spec fn smallest_missing_postcond(l: Seq<usize>, result: usize) -> bool {
    !l.contains(result) && 
    forall|candidate: usize| candidate < result ==> l.contains(candidate)
}

fn search(lst: &Vec<usize>, start_idx: usize, n: usize) -> (result: usize)
    requires 
        start_idx <= lst.len(),
    decreases lst.len() - start_idx
{
    if start_idx >= lst.len() {
        return start_idx;
    }
    
    if lst[start_idx] != start_idx {
        return start_idx;
    }
    
    search(lst, start_idx + 1, n)
}

fn smallest_missing(l: &Vec<usize>) -> (result: usize)
    requires smallest_missing_precond(l@)
    ensures smallest_missing_postcond(l@, result)
{
    let mut left = 0;
    let mut right = l.len();
    
    /* code modified by LLM (iteration 1): added decreases clause for binary search loop */
    while left < right 
        invariant 
            left <= right,
            right <= l.len(),
            forall|i: usize| i < left ==> i < l.len() && l@[i as int] == i,
            forall|i: usize| i >= right ==> i >= l.len() || l@[i as int] != i,
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if mid < l.len() && l[mid] == mid {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    left
}

}

fn main() {}