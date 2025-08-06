use vstd::prelude::*;

verus! {
    // Insertion sort.
    //
    // Author: Snorri Agnarsson, snorri@hi.is
    // Translated to Verus

    spec fn is_sorted(s: Seq<int>) -> bool {
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    }

    fn insertion_sort(s: &Vec<int>) -> (r: Vec<int>)
        ensures 
            s@.to_multiset() == r@.to_multiset(),
            is_sorted(r@),
    {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }
}

fn main() {}