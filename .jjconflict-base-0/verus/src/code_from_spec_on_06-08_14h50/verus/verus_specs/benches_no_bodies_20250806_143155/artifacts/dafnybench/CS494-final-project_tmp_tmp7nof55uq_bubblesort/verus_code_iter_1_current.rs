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
        let mut i = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                sorted(a@, i as int, n as int),
                forall|x: int, y: int| i <= x < n && 0 <= y < i ==> a@[y] <= a@[x],
        {
            let mut j = 0;
            
            while j < n - 1 - i
                invariant
                    0 <= i < n,
                    0 <= j <= n - 1 - i,
                    a.len() == n,
                    sorted(a@, (i + 1) as int, n as int),
                    forall|x: int, y: int| i <= x < n && 0 <= y < i ==> a@[y] <= a@[x],
                    forall|k: int| j < k < n - i ==> a@[j] <= a@[k],
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
        let mut vec = vec![3, 1, 4, 1, 5, 9, 2, 6];
        if vec.len() > 0 {
            bubble_sort(&mut vec);
        }
    }
}