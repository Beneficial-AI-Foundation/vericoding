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
use vstd::multiset::*;
#[verifier(nonlinear)]
proof fn lemma_multiset_inplace_swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let old_a_multiset = old(a)@.to_multiset();
    let new_a_multiset = a@.to_multiset();

    assert(a@.remove(i as int).remove(j as int).to_multiset() == old(a)@.remove(i as int).remove(j as int).to_multiset());
    assert(Multiset::singleton(a@[i as int]).add(Multiset::singleton(a@[j as int])) == Multiset::singleton(old(a)@[j as int]).add(Multiset::singleton(old(a)@[i as int])));
    assert(Multiset::singleton(a@[i as int]).add(Multiset::singleton(a@[j as int])).union(a@.remove(i as int).remove(j as int).to_multiset()) == new_a_multiset);
    assert(Multiset::singleton(old(a)@[i as int]).add(Multiset::singleton(old(a)@[j as int])).union(old(a)@.remove(i as int).remove(j as int).to_multiset()) == old_a_multiset);
}

proof fn lemma_multiset_vec_update<T>(a: &Vec<T>, i: usize, val: T)
    requires
        i < a.len(),
    ensures
        a.update(i as int, val).to_multiset() =~~= a.to_multiset(),
{
    // This lemma is a placeholder and ideally would be part of a standard library.
    // Verus often needs explicit proof for multiset equalities after updates.
    // For `Vec::swap`, `lemma_multiset_inplace_swap` is more direct.
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

    if n == 0 {
        return;
    }

    while n > 1
        invariant
            1 <= n <= old(a).len() + 1,
            // Elements from `n` to `a.len()` (exclusive) are sorted relative to each other and `a[n-1]` is the largest among `a[0..n]`.
            // More precisely, `a[n-1]` is in its final sorted position.
            sorted(a, n, a.len()),
            forall|x: int| 0 <= x < (n as int) ==> a[x] <= a[(n - 1) as int],
            forall|x: int, y: int| (0 <= x && x < (n as int)) && ((n as int) <= y && y < a.len() as int) ==> a[x] <= a[y],
            a@.to_multiset() == old(a)@.to_multiset(), // The multiset of elements remains unchanged
    {
        let mut i: usize = 0;
        let pvt_idx: usize = n - 1; // current "pivot" element is at index n-1

        while i < pvt_idx
            invariant
                0 <= i && i <= pvt_idx,
                pvt_idx == n - 1,
                // Elements from `n` to `old(a).len()` are sorted and larger than `a[0..n-1]`
                sorted(a, n, a.len()),
                forall|x: int, y: int| (0 <= x && x < (n as int)) && ((n as int) <= y && y < a.len() as int) ==> a[x] <= a[y],

                // Elements `a[0..i]` are sorted relative to one another, and each is less than or equal to `a[i]`
                // More specifically, `a[i]` is the largest among `a[0..i]`.
                forall|x: int| 0 <= x && x < (i as int) ==> a[x] <= a[i as int],

                a@.to_multiset() == old(a)@.to_multiset(), // The multiset of elements remains unchanged
        {
            if a[i] > a[i + 1] {
                a.swap(i, i + 1);
                lemma_multiset_inplace_swap(a, i, i + 1);
            }
            i = i + 1;
        }

        proof {
            // After inner loop, `a[n-1]` is the largest element in `a[0..n-1]`.
            assert(forall|x: int| 0 <= x < (n - 1) as int ==> a[x] <= a[(n - 1) as int]);

            // Prove that `a[n-1]` is less than or equal to all elements in the sorted suffix `a[n..a.len()]`.
            assert(forall|x: int, y: int| (0 <= x && x < (n as int)) && ((n as int) <= y && y < a.len() as int) ==> a[x] <= a[y]);
            assert(forall|y: int| (n as int) <= y && y < a.len() as int ==> a[(n - 1) as int] <= a[y]); // New property for the next outer loop iteration.

            // The sorted property for the tail remains.
            assert(sorted(a, n, a.len()));

            // Combine to show that the new 'sorted zone' including `n-1` is valid.
            // This prepares for `n` to become `n-1` in the next iteration.
            assert(sorted(a, n - 1, a.len()));
        }

        n = n - 1;
    }
    proof {
        assert(sorted(a, 0, a.len()));
    }
}
// </vc-code>

fn main() {
}

}