use vstd::prelude::*;

verus! {

/* 
* Formal verification of the selection sort algorithm with Verus.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn is_sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    assume(false);
    0
}

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a@, 0, a@.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let orig = a@;
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant is_sorted(a@, 0, i as int);
        invariant a@.to_multiset() == orig.to_multiset();
        invariant forall|k: int, l: int| 0 <= k && k < i as int && i as int <= l && l < n as int ==> a@[k] <= a@[l];
        decreases n - i;
    {
        // find index of minimum in [i, n)
        assert(i < n);
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant i <= m && m < n;
            invariant j <= n;
            invariant forall|k: int| (i as int) <= k && k < j as int ==> a@[k] >= a@[m as int];
            decreases n - j;
        {
            if a[j] < a[m] {
                m = j;
            }
            j = j + 1;
        }

        // capture old sequence before swap
        let old = a@;
        // swap minimum into position i
        a.swap(i, m);

        // prove preservation of invariants for next iteration (i -> i+1)
        proof {
            // From inner loop invariant at exit (j == n): every element in [i,n) is >= old[m]
            assert(forall|k: int| (i as int) <= k && k < (n as int) ==> old@[k] >= old@[m as int]);

            // From outer loop invariant before swap: prefix [0,i) is sorted
            assert(is_sorted(old, 0, i as int));
            // and also every element in prefix [0,i) is <= every element in suffix [i,n)
            assert(forall|k: int, l: int| 0 <= k && k < i as int && i as int <= l && l < n as int ==> old@[k] <= old@[l]);

            // name new array after swap
            let new = a@;

            // Prove new prefix [0, i+1) is sorted.
            assert(forall|u: int, v: int| 0 <= u && u < v && v < (i as int) + 1 ==>
                (if v < i as int {
                    old@[u] <= old@[v]
                } else {
                    // v == i
                    // new[i] == old[m], and for u < i we have old[u] <= old[m]
                    old@[u] <= old@[m as int]
                }
            ));
            assert(is_sorted(new, 0, (i as int) + 1));

            // Prove every element in new prefix [0, i+1) is <= every element in new suffix [i+1, n)
            assert(forall|k: int, l: int| 0 <= k && k < (i as int) + 1 && (i as int) + 1 <= l && l < (n as int) ==>
                (if k < i as int {
                    // when l == m, new[l] = old[i], but old[k] <= old[i] by outer invariant;
                    // when l != m, new[l] = old[l], and old[k] <= old[l] by outer invariant.
                    old@[k] <= (if l == m as int { old@[i as int] } else { old@[l] })
                } else {
                    // k == i: new[k] = old[m], and old[m] <= old[l] by inner invariant
                    old@[m as int] <= old@[l]
                }
            ));

            // Multiset preserved: Vec::swap preserves multiset, so new.to_multiset() == orig.to_multiset()
            assert(a@.to_multiset() == orig.to_multiset());
        }

        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}