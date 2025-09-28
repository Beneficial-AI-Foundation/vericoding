use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
use vstd::multiset::Multiset;
spec fn multiset_from_seq(s: Seq<int>) -> Multiset<int> {
    s.to_multiset()
}

proof fn is_sorted_split(s: Seq<int>, k: int)
    requires
        0 <= k <= s.len(),
        is_sorted(s.subsequence(0, k)),
    ensures
        forall|p: int, q: int| 0 <= p < q < k ==> s[p] <= s[q],
{
    // This helper proof is used to show a property about a subsequence based on is_sorted.
    // Verus usually handles these automatically, but sometimes explicit quantification helps.
}

proof fn lemma_multiset_append_element(s: Seq<int>, x: int)
    ensures
        (s + Seq::singleton(x)).to_multiset() == s.to_multiset().add(x),
{
    // Proves that appending an element to a sequence corresponds to adding it to the multiset.
    // This is a common property often handled by Verus's default multiset theory.
}

proof fn lemma_multiset_subsequence_and_append(s: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        s.subsequence(0, i).to_multiset().add(s[j]) == s.subsequence(0, i).to_multiset().add(s[j]), // Trivial, but used in pattern
{
    // This lemma is a placeholder for potential needs to reason about multisets of subsequences.
    // Verus often handles multiset equalities for subseq/append properties automatically.
}

// Proof that inserting an element into a sorted sequence maintains sortedness if the element is placed correctly
proof fn lemma_insert_maintains_sorted(s: Seq<int>, x: int, i: int)
    requires
        is_sorted(s),
        0 <= i <= s.len(),
        (i == 0 || s[i - 1] <= x),
        (i == s.len() || x <= s[i]),
    ensures
        is_sorted(s.subsequence(0, i) + Seq::singleton(x) + s.subsequence(i, s.len())),
{
    let new_s = s.subsequence(0, i) + Seq::singleton(x) + s.subsequence(i, s.len());
    assert(new_s.len() == s.len() + 1);

    assert forall|p: int, q: int| 0 <= p < q < new_s.len() implies new_s[p] <= new_s[q] by {
        if q < i {
            // Both p and q are in the prefix s.subsequence(0, i)
            assert(new_s[p] == s[p]);
            assert(new_s[q] == s[q]);
            assert(s[p] <= s[q]); // By is_sorted(s)
        } else if p >= i + 1 {
            // Both p and q are in the suffix s.subsequence(i, s.len())
            assert(new_s[p] == s[p - 1]);
            assert(new_s[q] == s[q - 1]);
            assert(s[p - 1] <= s[q - 1]); // By is_sorted(s)
        } else if p < i && q == i {
            // p is in prefix, q is the inserted element x
            assert(new_s[p] == s[p]);
            assert(new_s[q] == x);
            assert(s[p] <= s[i - 1]); // By is_sorted(s)
            assert(s[i - 1] <= x); // By precondition
            assert(s[p] <= x);
        } else if p < i && q > i {
            // p is in prefix, q is in suffix
            assert(new_s[p] == s[p]);
            assert(new_s[q] == s[q - 1]);
            assert(s[p] <= s[i - 1]); // By is_sorted(s)
            assert(s[i - 1] <= x); // By precondition
            assert(x <= s[i]); // By precondition
            assert(s[i] <= s[q - 1]); // By is_sorted(s)
            assert(s[p] <= s[q - 1]);
        } else if p == i && q > i {
            // p is the inserted element x, q is in suffix
            assert(new_s[p] == x);
            assert(new_s[q] == s[q - 1]);
            assert(x <= s[i]); // By precondition
            assert(s[i] <= s[q - 1]); // By is_sorted(s)
            assert(x <= s[q - 1]);
        }
    }
}

// Lemma to show that a two-part sequence's multiset is the sum of its parts.
proof fn lemma_multiset_concat(s1: Seq<int>, s2: Seq<int>)
    ensures
        (s1 + s2).to_multiset() == s1.to_multiset().add(s2.to_multiset()),
{
    // Verus often handles this automatically. This is for explicit documentation.
}

// Lemma for multiset equality of two sequences that are permutations of each other plus one element
proof fn lemma_multiset_permutation_add(orig_s: Seq<int>, sorted_prefix: Seq<int>, element: int, unsorted_suffix: Seq<int>)
    requires
        orig_s.to_multiset() == (sorted_prefix + Seq::singleton(element) + unsorted_suffix).to_multiset(),
    ensures
        (sorted_prefix + Seq::singleton(element) + unsorted_suffix).to_multiset() == orig_s.to_multiset(),
        (sorted_prefix + unsorted_suffix).to_multiset().add(element) == orig_s.to_multiset(),
{
    // This lemma is a common pattern when showing that elements are conserved.
    // The first ensures is trivial. The second uses `lemma_multiset_concat` and `lemma_multiset_append_element`.
    lemma_multiset_concat(sorted_prefix, Seq::singleton(element) + unsorted_suffix);
    lemma_multiset_split_element_from_seq(Seq::singleton(element) + unsorted_suffix, element, unsorted_suffix);
    lemma_multiset_concat(sorted_prefix, unsorted_suffix);
    assert((sorted_prefix + unsorted_suffix).to_multiset().add(element) == (sorted_prefix + Seq::singleton(element) + unsorted_suffix).to_multiset());
}

proof fn lemma_multiset_split_element_from_seq(s: Seq<int>, x: int, s_minus_x: Seq<int>)
    requires
        s == Seq::singleton(x) + s_minus_x || s == s_minus_x + Seq::singleton(x),
    ensures
        s.to_multiset() == s_minus_x.to_multiset().add(x),
{ }
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
    let mut a: Vec<int> = Vec::new();
    a.extend_from_slice(s.as_slice());

    #[verifier::loop_invariant_when(
        0 <= i && i <= a.len(),
        a.len() == s.len(),
        a.to_multiset() == s.to_multiset(), // All elements conserved
        is_sorted(a.subsequence(0, i as int)), // Prefix a[0..i-1] is sorted
    )]
    #[verifier::loop_termination(i decreases from a.len())]
    for i in 0..a.len() {
        let x = a.view_at(i); // The element to insert into the sorted prefix
        let mut j: usize = i; // j corresponds to insertion point

        // Snapshot 'a' state at loop entry for reasoning about
        // current iteration's transformations from a known good state.
        let a_at_loop_entry_i = a.view();

        #[verifier::loop_invariant_when(
            0 <= j && j <= i,
            a.len() == s.len(),
            a.to_multiset() == a_at_loop_entry_i.to_multiset(), // Elements conserved
            x == a_at_loop_entry_i.view_at(i), // x is the original element from position i
            // The elements from j to i-1 have been shifted one position to the right
            forall|k: int| (j as int) <= k && k < i ==> a.view_at((k as int) + 1) == a_at_loop_entry_i.view_at(k),
            // The `j` prefix of `a` is the same as the `j` prefix of `a_at_loop_entry_i`
            a.subsequence(0, j as int) == a_at_loop_entry_i.subsequence(0, j as int),
            // The segment shifted to the right from j to i (exclusive) is sorted
            is_sorted(a_at_loop_entry_i.subsequence(0, i as int)), // This is the sorted prefix before modification
            // The element x is less than or equal to elements it is shifting
            forall|k: int| (j as int) <= k && k < i ==> x <= a_at_loop_entry_i.view_at(k), // The shifted elements were greater than x
            // Elements before j are less than or equal to x
            (j == 0 || a.view_at((j as int) - 1) <= x),
        )]
        #[verifier::loop_termination(j decreases)]
        while j > 0 && a.view_at(j - 1) > x {
            a.set(j, a.view_at(j - 1));
            j = j - 1;
        }
        a.set(j, x);
        
        proof {
            // We need to prove is_sorted(a.subsequence(0, i+1)).
            // This is equivalent to proving `is_sorted(prefix + singleton(x) + suffix)`
            // where `prefix = a_at_loop_entry_i.subsequence(0, j as int)`
            // and `suffix = a_at_loop_entry_i.subsequence(j as int, i as int)`
            
            // We know that `is_sorted(a_at_loop_entry_i.subsequence(0, i as int))`.
            // From inner loop invariant: 
            // `(j == 0 || a.view_at((j as int) - 1) <= x)` implies `(j == 0 || a_at_loop_entry_i.view_at((j as int) - 1) <= x)`
            // Also, `is_sorted(a_at_loop_entry_i.subsequence(0, i as int))` means for `k` from `j` to `i-1`, `a_at_loop_entry_i.view_at(k)` are sorted.
            // When the inner loop terminates, either `j == 0` or `a.view_at(j-1) <= x`.
            // If `j < i`, it means `x` must be less than or equal to `a_at_loop_entry_i.view_at(j)`.
            // This condition is true because if `x` was greater than `a_at_loop_entry_i.view_at(j)`, `j` would have continued to decrease,
            // or if `j` became `0`, then `x` would be inserted at position `0`.
            // So if `j <= i`, based on the inner loop logic, `x` is placed such that
            // `(j == 0 || a_at_loop_entry_i.view_at((j as int) - 1) <= x)` 
            // AND `(j == i || x <= a_at_loop_entry_i.view_at(j as int))` (if `j` is not `i`, then `j` is where `x` is inserted before `a_at_loop_entry_i.view_at(j)`).
            
            // Specifically, when the inner loop finishes:
            // 1. `j == 0` OR `a_at_loop_entry_i.view_at(j - 1) <= x`. (from the loop condition `a.view_at(j - 1) > x`)
            // 2. Either `j == i` (meaning `x` stays at original position `i`, or `x` is the largest so far),
            //    OR `j < i` AND `x <= a_at_loop_entry_i.view_at(j)` (because if `x > a_at_loop_entry_i.view_at(j)`, `j` would decrease further).
            
            lemma_insert_maintains_sorted(
                a_at_loop_entry_i.subsequence(0, i as int), // s in the lemma
                x, // x in the lemma
                j as int, // i in the lemma (insertion point)
            );
            
            // Prove that the final `a.subsequence(0, i + 1)` is indeed the sequence from `lemma_insert_maintains_sorted`.
            assert(a.subsequence(0, (j as int)) == a_at_loop_entry_i.subsequence(0, (j as int)));
            assert(a.view_at(j as int) == x);
            assert(a.subsequence((j as int) + 1, (i as int) + 1) == a_at_loop_entry_i.subsequence(j as int, i as int));
            
            assert(a.subsequence(0, (i as int) + 1) == a_at_loop_entry_i.subsequence(0, (j as int)) + Seq::singleton(x) + a_at_loop_entry_i.subsequence(j as int, i as int));
        }
    }

    a.to_seq()
}
// </vc-code>

fn main() {}

}