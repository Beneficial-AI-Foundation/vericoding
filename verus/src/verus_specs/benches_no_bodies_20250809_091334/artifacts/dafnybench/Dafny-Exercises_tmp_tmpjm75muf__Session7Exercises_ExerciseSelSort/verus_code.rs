use vstd::prelude::*;

verus! {
    // Predicate to check if a segment of array is sorted
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool 
        recommends 0 <= i <= j <= a.len()
    {
        forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
    }

    fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
        requires 
            c <= f,
            f <= old(a).len(),
        ensures 
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, f as int),
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}