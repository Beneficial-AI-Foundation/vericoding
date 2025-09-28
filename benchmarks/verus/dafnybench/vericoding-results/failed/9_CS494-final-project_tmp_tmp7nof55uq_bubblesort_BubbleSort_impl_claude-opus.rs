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
// Helper lemma to show that swapping two elements preserves the multiset
proof fn swap_preserves_multiset(a: &Vec<i32>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() =~= a@.update(i as int, a@[j as int]).update(j as int, a@[i as int]).to_multiset(),
{
    // Verus can prove this automatically
}

// Helper lemma showing that if we have sorted(a, i, n) and pivot(a, n, i-1),
// then we have sorted(a, i-1, n) after ensuring a[i-2] <= a[i-1]
proof fn extend_sorted(a: &Vec<i32>, i: usize, n: usize)
    requires
        1 < i <= n,
        n == a.len(),
        sorted(a, i, n),
        pivot(a, n, (i - 1) as usize),
        i >= 2,
        forall|k: usize| i - 1 <= k < n ==> a@[(i - 2) as int] <= a@[k as int],
    ensures
        sorted(a, (i - 1) as usize, n),
        i >= 2 ==> pivot(a, n, (i - 2) as usize),
{
    // This proves that we can extend the sorted region
}

// Helper to show pivot property is preserved after swap
proof fn swap_preserves_pivot_below(a: &Vec<i32>, j: usize, i: usize, n: usize, a_new: &Vec<i32>)
    requires
        1 <= j < i <= n,
        n == a.len(),
        n == a_new.len(),
        j >= 1,
        a@[(j - 1) as int] > a@[j as int],
        pivot(a, i, (j - 1) as usize),
        a_new@ == a@.update((j - 1) as int, a@[j as int]).update(j as int, a@[(j - 1) as int]),
    ensures
        pivot(a_new, i, j),
{
    // After swapping a[j-1] and a[j], the pivot property shifts
}

// Helper to maintain sorted property after swap
proof fn swap_preserves_sorted(a: &Vec<i32>, j: usize, i: usize, n: usize, a_new: &Vec<i32>)
    requires
        1 <= j < i <= n,
        n == a.len(),
        n == a_new.len(),
        sorted(a, i, n),
        a_new@ == a@.update((j - 1) as int, a@[j as int]).update(j as int, a@[(j - 1) as int]),
    ensures
        sorted(a_new, i, n),
{
    // Swapping elements before index i doesn't affect sorted(a, i, n)
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
    
    while i > 1
        invariant
            1 <= i <= n,
            n == a.len(),
            sorted(a, i, n),
            i < n ==> pivot(a, n, (i - 1) as usize),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut j: usize = 1;
        
        while j < i
            invariant
                1 <= j <= i,
                1 <= i <= n,
                n == a.len(),
                sorted(a, i, n),
                j > 1 ==> pivot(a, i, (j - 1) as usize),
                j > 1 ==> forall|k: usize| j - 1 <= k < i ==> #[trigger] a@[(j - 2) as int] <= a@[k as int],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[(j - 1) as usize] > a[j] {
                // Need to swap
                let old_a = a@;
                
                let temp = a[(j - 1) as usize];
                a.set((j - 1) as usize, a[j]);
                a.set(j, temp);
                
                proof {
                    swap_preserves_multiset(&vec![old_a[(j - 1) as int], old_a[j as int]], 0, 1);
                    assert(a@ == old_a.update((j - 1) as int, old_a[j as int]).update(j as int, old_a[(j - 1) as int]));
                    if j > 1 {
                        swap_preserves_pivot_below(&vec(old_a), j, i, n, a);
                    }
                    swap_preserves_sorted(&vec(old_a), j, i, n, a);
                }
                
                assert(a@[(j - 1) as int] <= a@[j as int]);
            }
            
            assert(a@[(j - 1) as int] <= a@[j as int]);
            
            j = j + 1;
        }
        
        assert(j == i);
        assert(forall|k: usize| i - 1 <= k < i ==> a@[(i - 2) as int] <= a@[k as int]);
        assert(forall|k: usize| i - 1 <= k < n ==> a@[(i - 2) as int] <= a@[k as int]);
        
        proof {
            if i > 1 {
                extend_sorted(a, i, n);
            }
        }
        
        i = i - 1;
    }
    
    assert(i == 1);
    assert(sorted(a, 1, n));
    assert(sorted(a, 0, n));
}
// </vc-code>

fn main() {
}

}