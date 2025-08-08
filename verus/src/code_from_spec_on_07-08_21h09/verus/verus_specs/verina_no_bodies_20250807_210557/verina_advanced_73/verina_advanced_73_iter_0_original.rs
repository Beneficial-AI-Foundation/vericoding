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
    return 0;  // TODO: Remove this line and implement the function body
}

fn smallest_missing(l: &Vec<usize>) -> (result: usize)
    requires smallest_missing_precond(l@)
{
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}