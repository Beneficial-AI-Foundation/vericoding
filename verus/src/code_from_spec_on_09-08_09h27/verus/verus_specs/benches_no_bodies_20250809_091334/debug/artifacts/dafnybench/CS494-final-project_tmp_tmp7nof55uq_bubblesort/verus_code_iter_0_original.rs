use vstd::prelude::*;

verus! {
    // Predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array
    spec fn sorted(a: Seq<int>, from: int, to: int) -> bool
        recommends 0 <= from <= to <= a.len()
    {
        forall|x: int, y: int| from <= x < y < to ==> a[x] <= a[y]
    }

    // Helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
    spec fn pivot(a: Seq<int>, to: int, pvt: int) -> bool
        recommends 0 <= pvt < to <= a.len()
    {
        forall|x: int, y: int| 0 <= x < pvt < y < to ==> a[x] <= a[y]
    }

    // Here having the algorithm for the bubblesort
    fn bubble_sort(a: &mut Vec<int>)
        requires 
            old(a).len() > 0,
        ensures 
            sorted(a@, 0, a.len() as int),
            a.len() == old(a).len(),
    {
    // TODO: Remove this comment and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}