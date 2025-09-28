use vstd::prelude::*;

verus! {

//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785


// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|x: usize, y: usize| from <= x < y < to ==> a[x as int] <= a[y as int]
}

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
spec fn pivot(a: &Vec<i32>, to: usize, pvt: usize) -> bool
    recommends
        pvt < to,
        to <= a.len(),
{
    forall|x: usize, y: usize| 0 <= x < pvt < y < to ==> a[x as int] <= a[y as int] // all values within the array should be in ascending order
}

// Here having the algorithm for the bubblesort

// <vc-helpers>
spec fn partitioned(a: &Vec<i32>, pivot_idx: usize, to: usize) -> bool
    recommends
        pivot_idx < to,
        to <= a.len(),
{
    forall|x: usize| x < pivot_idx ==> a[x as int] <= a[pivot_idx as int] &&
    forall|y: usize| pivot_idx < y < to ==> a[pivot_idx as int] <= a[y as int]
}

proof fn lemma_sorted_implies_partitioned(a: &Vec<i32>, from: usize, to: usize)
    requires
        sorted(a, from, to),
        from <= to,
        to <= a.len(),
    ensures
        forall|p: usize| from <= p < to ==> partitioned(a, p, to)
{
}

proof fn lemma_swap_preserves_multiset(a: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset()
{
}

proof fn lemma_bubble_up_preserves_multiset(a: &mut Vec<i32>, to: usize)
    requires
        to <= a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset()
{
}

proof fn lemma_bubble_up_establishes_pivot(a: &mut Vec<i32>, to: usize)
    requires
        to <= a.len(),
        to > 0,
    ensures
        partitioned(a, to-1, to)
{
}

proof fn lemma_sorted_range_extension(a: &Vec<i32>, from: usize, mid: usize, to: usize)
    requires
        from <= mid <= to,
        to <= a.len(),
        sorted(a, from, mid),
        sorted(a, mid, to),
        partitioned(a, mid-1, to),
    ensures
        sorted(a, from, to)
{
}
// </vc-helpers>

// <vc-spec>
fn BubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0, // makes sure a is not empty and length is greater than 0
    ensures 
        sorted(a, 0, a.len()), // makes sure elements of array a are sorted from 0 - a.len()
        a@.to_multiset() == old(a)@.to_multiset(), // Since a is being modified, we compare the previous elements to current elements.
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = n;
    
    while i > 0
        invariant
            i <= n,
            sorted(a, i, n),
            forall|p: usize| i <= p < n ==> partitioned(a, p, n),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        i = i - 1;
        let mut j: usize = 0;
        
        while j < i
            invariant
                j <= i,
                i < n,
                sorted(a, i, n),
                partitioned(a, i, n),
                forall|k: usize| k < j ==> a[k as int] <= a[j as int],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j as int] > a[(j+1) as int] {
                let temp = a[j];
                a[j] = a[j+1];
                a[j+1] = temp;
                proof { lemma_swap_preserves_multiset(a, j, j+1); }
            }
            j = j + 1;
        }
        
        proof { lemma_bubble_up_establishes_pivot(a, i+1); }
    }
}
// </vc-code>

fn main() {
}

}