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
// Helper lemma to prove that swapping two adjacent elements preserves the multiset
proof fn swap_preserves_multiset(a: &Vec<i32>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.update(i as int, a[j as int]).update(j as int, a[i as int]).to_multiset() == a@.to_multiset()
{
    let original = a@;
    let swapped = original.update(i as int, a[j as int]).update(j as int, a[i as int]);
    
    assert(swapped.to_multiset() =~= original.to_multiset());
}

// Helper lemma to prove that if we have a sorted range and pivot property, 
// extending the sorted range maintains sortedness
proof fn extend_sorted_range(a: &Vec<i32>, from: usize, to: usize, new_to: usize)
    requires
        from <= to <= new_to <= a.len(),
        sorted(a, from, to),
        to < new_to ==> forall|x: usize| from <= x < to ==> #[trigger] a[x as int] <= a[to as int],
    ensures
        to == new_to ==> sorted(a, from, new_to),
        to < new_to && sorted(a, to, new_to) ==> sorted(a, from, new_to),
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
    let mut n = a.len();
    
    while n > 1
        invariant
            1 <= n <= a.len(),
            sorted(a, n, a.len()),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: usize, j: usize| n <= i < a.len() && 0 <= j < n ==> #[trigger] a[j as int] <= #[trigger] a[i as int],
        decreases n,
    {
        let mut i = 0;
        
        while i < n - 1
            invariant
                0 <= i < n,
                n <= a.len(),
                sorted(a, n, a.len()),
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: usize, j: usize| n <= k < a.len() && 0 <= j < n ==> #[trigger] a[j as int] <= #[trigger] a[k as int],
                forall|x: usize, y: usize| 0 <= x < y <= i ==> #[trigger] a[x as int] <= #[trigger] a[y as int],
                forall|k: usize| 0 <= k <= i && i + 1 < n ==> #[trigger] a[k as int] <= a[(i + 1) as int],
            decreases n - 1 - i,
        {
            if a[i] > a[i + 1] {
                // Swap elements
                let temp = a[i];
                let temp2 = a[i + 1];
                a.set(i, temp2);
                a.set(i + 1, temp);
                
                proof {
                    swap_preserves_multiset(old(a), i, (i + 1) as usize);
                }
            }
            i = i + 1;
        }
        
        assert(sorted(a, (n - 1) as usize, a.len()));
        assert(forall|j: usize| 0 <= j < n - 1 ==> #[trigger] a[j as int] <= a[(n - 1) as int]);
        
        n = n - 1;
    }
    
    assert(n == 1);
    assert(sorted(a, 1, a.len()));
    assert(sorted(a, 0, a.len()));
}
// </vc-code>

fn main() {
}

}