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
        let n = a.len();
        let mut i: usize = 0;
        
        while i < n
            invariant
                i <= n,
                a.len() == n,
                sorted(a@, (n - i) as int, n as int),
                forall|x: int, y: int| (n - i) as int <= x < n as int && 0 <= y < (n - i) as int ==> a@[y] <= a@[x]
        {
            let mut j: usize = 0;
            
            while j < n - 1 - i
                invariant
                    j <= n - 1 - i,
                    i < n,
                    a.len() == n,
                    sorted(a@, (n - i) as int, n as int),
                    forall|x: int, y: int| (n - i) as int <= x < n as int && 0 <= y < (n - i) as int ==> a@[y] <= a@[x],
                    /* code modified by LLM (iteration 1): fixed type mismatch by casting j to int */
                    forall|k: int| 0 <= k < j as int ==> a@[k] <= a@[j as int]
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
        /* code modified by LLM (iteration 2): explicitly specify Vec<int> type to match bubble_sort parameter */
        let mut vec: Vec<int> = vec![64, 34, 25, 12, 22, 11, 90];
        bubble_sort(&mut vec);
    }
}