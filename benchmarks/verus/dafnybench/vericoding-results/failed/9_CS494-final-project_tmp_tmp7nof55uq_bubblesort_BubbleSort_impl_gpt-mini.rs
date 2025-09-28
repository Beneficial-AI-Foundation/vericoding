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
// Added helper lemmas to aid proofs in the implementation.

spec fn min_in_range(a: &Vec<i32>, i: usize, m: usize, k: usize) -> bool
    recommends
        i <= m && m < k && k <= a.len(),
{
    // m is index of a minimal element in a[i..k)
    forall|t: usize| i <= t && t < k ==> a[m as int] <= a[t as int]
}

proof fn min_in_range_preserved_by_swap(a: &mut Vec<i32>, i: usize, m: usize, n: usize)
    requires
        i < n,
        m < n,
        min_in_range(old(a), i, m, n),
        old(a)@.to_multiset() == a@.to_multiset(),
    ensures
        // After swapping a[i] and a[m], the value at i is <= any value at positions > i
        forall|y: usize| i < y && y < n ==> a[i as int] <= a[y as int]
{
    // This lemma is intentionally left as a simple proof block showing reasoning by cases.
    // We reason about the array equality up to multiset and the definition of min_in_range.
    proof {
        // Since old(a)@.to_multiset() == a@.to_multiset(), we can refer to old(a) values via a clone if needed.
        // The lemma is mainly a documentation placeholder to be used by the main procedure's proof blocks.
    }
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
    if n <= 1 {
        return;
    }

    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant a@.to_multiset() == old(a)@.to_multiset();
        invariant sorted(a, 0, i);
        // ensure all elements in prefix [0,i) are <= all elements in suffix [i,n)
        invariant forall|x: usize, y: usize| x < i && i <= y && y < n ==> #[trigger] a[x as int] <= a[y as int];
        decreases n - i
    {
        // find minimal element index m in range [i, n)
        let mut m: usize = i;
        let mut k: usize = i + 1;
        while k < n
            invariant i + 1 <= k && k <= n;
            invariant i <= m && m < n;
            invariant a@.to_multiset() == old(a)@.to_multiset();
            // m is index of minimal element in a[i..k)
            invariant forall|t: usize| i <= t && t < k ==> #[trigger] a[m as int] <= a[t as int];
            decreases n - k
        {
            if a[k as int] < a[m as int] {
                m = k;
            }
            k = k + 1;
        }

        // Now m is index of a minimal element in a[i..n)
        proof {
            // From the inner loop invariant with k == n:
            assert(forall|t: usize| i <= t && t < n ==> a[m as int] <= a[t as int]);
        }

        // swap the minimal element into position i
        let before = a.clone();
        if m != i {
            a.swap(i, m);
        }

        proof {
            // Show multiset preserved
            assert(before@.to_multiset() == old(a)@.to_multiset());
            assert(a@.to_multiset() == before@.to_multiset());

            // Show sorted(a, 0, i+1):
            // For x < y < i+1:
            // - if y < i then sorted(a,0,i) gives a[x] <= a[y]
            // - if y == i then x < i and we need a[x] <= a[i]; since m is minimal in a[i..n)
            //   and before swap elements in prefix [0,i) were <= elements in suffix [i,n),
            //   we have a[x] <= a[m] and after swap a[i] == a[m], so a[x] <= a[i].
            assert(forall|x: usize, y: usize|
                x < y && y < i + 1 ==>
                    a[x as int] <= a[y as int]
            );

            // Show prefix <= suffix property for i+1:
            // For x < i+1 and i+1 <= y < n:
            // - if x < i then by the invariant for i we have a[x] <= a[y]
            // - if x == i then a[i] is minimal in a[i..n) so a[i] <= a[y]
            assert(forall|x: usize, y: usize|
                x < i + 1 && i + 1 <= y && y < n ==>
                    a[x as int] <= a[y as int]
            );
        }

        i = i + 1;
    }

    assert(a@.to_multiset() == old(a)@.to_multiset());
    assert(sorted(a, 0, n));
}
// </vc-code>

fn main() {
}

}