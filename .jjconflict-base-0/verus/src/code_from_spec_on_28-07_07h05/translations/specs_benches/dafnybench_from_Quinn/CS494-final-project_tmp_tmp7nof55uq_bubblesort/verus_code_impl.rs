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
    //IMPL bubble_sort
    fn bubble_sort(a: &mut Vec<int>)
        requires 
            old(a).len() > 0,
        ensures 
            sorted(a@, 0, a.len() as int),
            a.len() == old(a).len(),
    {
        let mut i = 0;
        while i < a.len()
            invariant
                a.len() == old(a).len(),
                sorted(a@, (a.len() - i) as int, a.len() as int),
                forall|x: int, y: int| (a.len() - i) as int <= x < a.len() && 0 <= y < (a.len() - i) as int ==> a[y] <= a[x],
        {
            let mut j = 0;
            while j < a.len() - 1 - i
                invariant
                    a.len() == old(a).len(),
                    sorted(a@, (a.len() - i) as int, a.len() as int),
                    forall|x: int, y: int| (a.len() - i) as int <= x < a.len() && 0 <= y < (a.len() - i) as int ==> a[y] <= a[x],
                    /* code modified by LLM (iteration 1): Fixed type mismatch by using j as usize for array indexing */
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int],
            {
                if a[j] > a[j + 1] {
                    let temp = a[j];
                    a.set(j, a[j + 1]);
                    a.set(j + 1, temp);
                }
                j += 1;
            }
            i += 1;
        }
    }

    fn main() {
        /* code modified by LLM (iteration 2): Fixed invalid int suffix by removing int suffixes from number literals */
        let mut vec: Vec<int> = vec![64, 34, 25, 12, 22, 11, 90];
        bubble_sort(&mut vec);
    }
}