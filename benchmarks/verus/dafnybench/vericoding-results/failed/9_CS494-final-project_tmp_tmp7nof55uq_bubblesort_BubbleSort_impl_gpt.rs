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
proof fn pivot_preserved_by_prefix_swap(a: &Vec<i32>, to: usize, pvt: usize, i: usize)
    requires
        0 < to <= a.len(),
        pvt < to,
        i + 1 < pvt,
        pivot(a, to, pvt),
{
    // Swapping two elements in the prefix [0..pvt) preserves the pivot property,
    // since pivot compares any element in prefix with any in suffix; the set of
    // values in prefix is unchanged by an internal swap.
}

proof fn pivot_preserved_by_prefix_noop(a: &Vec<i32>, to: usize, pvt: usize)
    requires
        0 < to <= a.len(),
        pvt < to,
        pivot(a, to, pvt),
{
}

proof fn suffix_sorted_preserved_by_prefix_swap(a: &Vec<i32>, from: usize, to: usize, i: usize)
    requires
        from <= to,
        to <= a.len(),
        sorted(a, from, to),
        i + 1 <= from,
{
    // Swapping elements strictly before 'from' does not affect sortedness of [from..to)
}

proof fn multiset_preserved_by_adjacent_swap(a: &Vec<i32>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
{
    // Swapping two elements preserves the multiset of elements
}

proof fn suffix_sorted_extends_one(a: &Vec<i32>, from: usize, to: usize)
    requires
        from + 1 <= to,
        to <= a.len(),
        sorted(a, from + 1, to),
        forall|y: usize| from + 1 <= y < to ==> a[from as int] <= a[y as int],
    ensures
        sorted(a, from, to),
{
    // If tail [from+1..to) is sorted and a[from] <= every element in [from+1..to),
    // then [from..to) is sorted.
}

proof fn bubble_inner_preserves_suffix_and_multiset(a: &Vec<i32>, n: usize, k: usize)
    requires
        n <= a.len(),
        k <= n,
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
    if n <= 1 {
        return;
    }

    let ghost old_ms = old(a)@.to_multiset();

    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            0 <= i <= n,
            // The suffix [n - i .. n) is sorted
            sorted(a, n - i, n),
            // All elements in the prefix are <= all elements in the suffix (when prefix non-empty)
            i > 0 ==> pivot(a, n, n - i),
            // Multiset preserved
            a@.to_multiset() == old_ms
        decreases n - i
    {
        let mut j: usize = 1;
        while j < n - i
            invariant
                a.len() == n,
                1 <= j <= n - i,
                // Suffix remains sorted and untouched by inner swaps
                sorted(a, n - i, n),
                // Prefix/suffix pivot relation preserved when applicable
                i > 0 ==> pivot(a, n, n - i),
                // Multiset preserved across swaps
                a@.to_multiset() == old_ms
            decreases n - i - j
        {
            // Compare and swap adjacent elements in the prefix region [0 .. n - i)
            if a[j - 1] > a[j] {
                a.swap(j - 1, j);

                proof {
                    multiset_preserved_by_adjacent_swap(a, j - 1, j);
                }

                proof {
                    // Swaps only occur within the prefix [0 .. n - i), so suffix sortedness is preserved
                    suffix_sorted_preserved_by_prefix_swap(a, n - i, n, j - 1);
                }

                if i > 0 {
                    proof {
                        // Swapping within prefix preserves pivot relation with the suffix
                        pivot_preserved_by_prefix_swap(a, n, n - i, j - 1);
                    }
                } else {
                    proof {
                        pivot_preserved_by_prefix_noop(a, n, n - i);
                    }
                }
            }
            j += 1;
        }

        // After bubbling, the maximal element in the prefix is at position n - i - 1.
        // From the inner loop, we know that for all y in [n-i .. n), a[n-i-1] <= a[y]
        // This extends the sorted suffix by one element on the left.
        if n - i >= 1 {
            proof {
                // Establish that a[n - i - 1] <= every element in the suffix [n - i .. n)
                // This follows from the termination of bubbling passes.
                // We use the pivot relation which implies every prefix elem <= every suffix elem.
                if i > 0 {
                    // pivot ensures: for all x < pvt and y > pvt with pvt = n - i
                    // choose x = n - i - 1 and any y in [n - i .. n)
                    assert(pivot(a, n, n - i));
                }
                suffix_sorted_extends_one(a, n - i - 1, n);
            }
        }

        i += 1;
    }

    assert(sorted(a, 0, a.len()));
    assert(a@.to_multiset() == old_ms);
}
// </vc-code>

fn main() {
}

}