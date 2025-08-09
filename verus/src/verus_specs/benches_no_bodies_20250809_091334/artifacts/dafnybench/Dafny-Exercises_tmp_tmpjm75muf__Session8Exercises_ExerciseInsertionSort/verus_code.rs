use vstd::prelude::*;

verus! {
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
        recommends 0 <= i <= j + 1 <= a.len()
    {
        forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
    }

    fn insertion_sort(a: &mut Vec<int>)
        requires old(a).len() > 0,
        ensures 
            sorted_seg(a@, 0, a.len() as int - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}