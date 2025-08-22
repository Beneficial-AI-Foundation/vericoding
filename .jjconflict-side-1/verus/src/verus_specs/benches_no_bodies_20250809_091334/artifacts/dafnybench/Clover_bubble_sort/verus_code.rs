use vstd::prelude::*;

verus! {
    fn bubble_sort(a: &mut Vec<i32>)
        requires old(a).len() >= 0,
        ensures 
            // Array is sorted
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
            // Length is preserved
            a.len() == old(a).len(),
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}