use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_sorted(a: &Vec<i32>) -> bool {
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i && (i as int) < a.len() as int,
            forall|j: int, k: int| 0 <= j && (j as usize) < a.len() && 0 <= k && (k as usize) < a.len() && j < k && (k as int) <= i as int + 1 ==> a[j as usize] <= a[k as usize],
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

proof fn lemma_multiset_permutes_swap(
    a: &mut Vec<i32>,
    i: int,
    j: int,
    k: int,
    l: int,
)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        i < j,
        a@.to_multiset() == old(a)@.to_multiset(),
        k == i,
        l == j,
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    // This lemma is implicitly handled by Verus's default reasoning about `vec_insert` and `vec_remove`
    // when applied to swaps. Verus knows that `vec_swap` operation preserves multiset equality.
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n <= 1 {
        // Already sorted or empty, and multiset is preserved
        return;
    }

    let mut i: usize = n - 1;
    while i >= 1
        invariant
            (i as int) >= 0 && (i as int) < n as int,
            // Elements from i to n-1 are in their final sorted positions relative to each other
            forall|x: int, y: int| (i as int) <= x && x < y && (y as usize) < n ==> a[x as usize] <= a[y as usize],
            // Overall permutation property
            a@.to_multiset() == old(a)@.to_multiset(),
            // All elements from 0 to i-1 are less than or equal to elements from i to n-1
            forall|x: int, y: int| 0 <= x && (x as usize) < i && (i as int) <= y && (y as usize) < n ==> a[x as usize] <= a[y as usize],
    {
        let mut j: usize = 0;
        while j < i
            invariant
                (j as int) >= 0 && (j as int) <= (i as int),
                // The largest element in a[0..i] has "bubbled up" to a[j] or further
                forall|k: int| 0 <= k && (k as usize) < j ==> a[k as usize] <= a[j as usize],
                // Overall permutation property
                a@.to_multiset() == old(a)@.to_multiset(),
                // Elements from i to n-1 are in their final sorted positions relative to each other
                forall|x: int, y: int| (i as int) <= x && x < y && (y as usize) < n ==> a[x as usize] <= a[y as usize],
                // All elements from 0 to i-1 are less than or equal to elements from i to n-1
                forall|x: int, y: int| 0 <= x && (x as usize) < i && (i as int) <= y && (y as usize) < n ==> a[x as usize] <= a[y as usize],
        {
            if a[j] > a[j+1] {
                a.swap(j, j+1);
            }
            j = j + 1;
        }
        i = i - 1;
    }

    // After the loops, prove the final sorted property
    proof {
        assert(is_sorted(a));
        assert(forall|k: int| 0 <= k && (k as usize) < n - 1 ==> a[k as usize] <= a[(k+1) as usize]);
        assert(forall|x: int, y: int| 0 <= x && (x as usize) < n && 0 <= y && (y as usize) < n && x < y ==> a[x as usize] <= a[y as usize]);
    }
}
// </vc-code>

fn main() {
}

}