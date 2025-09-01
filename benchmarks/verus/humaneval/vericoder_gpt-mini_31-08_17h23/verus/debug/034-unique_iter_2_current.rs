use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
fn min_index(v: &Vec<i32>) -> (res: int)
    requires
        v.len() > 0,
    ensures
        0 <= res && res < v.len(),
    ensures
        forall|j: int| 0 <= j < v.len() ==> v@[res] <= v@[j],
{
    let mut idx: int = 0;
    let mut i: int = 1;
    // Invariant: idx is index of minimal element among v@[0..i)
    while i < v.len() {
        invariant 0 <= idx && idx < v.len();
        invariant 1 <= i && i <= v.len();
        invariant forall|j: int| 0 <= j < i ==> v@[idx] <= v@[j];
        let vi = v@[i];
        let v_idx = v@[idx];
        if vi < v_idx {
            idx = i;
        }
        i += 1;
    }
    idx
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
{
    // impl-start
    // Phase 1: build `rem` as the distinct elements seen in `s` (order arbitrary)
    let mut rem: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < s.len() {
        invariant 0 <= i && i <= s.len();
        // Every seen element is represented in rem
        invariant forall|k: int| 0 <= k < i ==> rem@.contains(s@[k]);
        // Every element in rem comes from some seen index < i
        invariant forall|y: i32| rem@.contains(y) ==> exists|k: int| 0 <= k < i && s@[k] == y;
        // rem has distinct elements
        invariant forall|p: int, q: int| 0 <= p < q < rem.len() ==> rem@[p] != rem@[q];
        let x = s@[i];
        if !rem@.contains(x) {
            // After push, new element x is in rem and corresponds to index i
            rem.push(x);
            // proof of the existential part for the invariant: the newly pushed element corresponds to index i
            proof {
                assert(rem@.contains(x));
                assert(exists|k: int| 0 <= k && k < i + 1 && s@[k] == x);
                // witness is i
            }
        }
        i += 1;
    }

    // Snapshot the distinct elements of s
    let initial: Vec<i32> = rem.clone();

    // Phase 2: repeatedly remove the minimum from rem and append to result
    let mut result: Vec<i32> = Vec::new();
    // Loop while rem not empty: maintain that result contains smallest extracted elements in strictly increasing order,
    // and rem contains the remaining distinct elements from `initial`.
    while rem.len() > 0 {
        invariant 0 <= rem.len() && rem.len() <= initial.len();
        invariant 0 <= result.len() && result.len() <= initial.len();
        invariant result.len() + rem.len() == initial.len();
        invariant forall|y: i32| result@.contains(y) ==> initial@.contains(y);
        invariant forall|y: i32| rem@.contains(y) ==> initial@.contains(y);
        invariant forall|y: i32| initial@.contains(y) ==> result@.contains(y) || rem@.contains(y);
        invariant forall|p: int, q: int| 0 <= p < q < result.len() ==> result@[p] < result@[q];
        invariant forall|p: int, q: int| 0 <= p < q < rem.len() ==> rem@[p] != rem@[q];
        // If result non-empty, its last element is strictly smaller than every element remaining in rem
        invariant (result.len() == 0) || (forall|y: i32| rem@.contains(y) ==> result@[result.len() - 1] < y);

        // Snapshot rem before removal to reason about indices after removal
        let old_rem: Vec<i32> = rem.clone();
        let mi = min_index(&old_rem);
        // mi is valid and old_rem@[mi] is minimal among old_rem
        assert(0 <= mi && mi < old_rem.len());
        let mv = rem.remove(mi);
        // mv came from old_rem at index mi
        assert(mv == old_rem@[mi]);
        // mv came from rem, so it is in initial
        assert(initial@.contains(mv));

        // Push mv onto result; must show new sortedness and invariants preserved.
        // If result was non-empty, its last element < mv by invariant, so ordering preserved.
        result.push(mv);

        // After removal, mv is no longer in rem, and every remaining element in rem is strictly greater than mv,
        // because mv was minimal and rem had distinct elements.
        proof {
            // show: forall y in rem, mv < y
            assert(forall|y: i32| rem@.contains(y) ==> old_rem@.contains(y));
            // For any y in rem, it corresponds to some index k in old_rem with k != mi
            assert(forall|y: i32| rem@.contains(y) ==> exists|k: int| 0 <= k < old_rem.len() && k != mi && old_rem@[k] == y);
            // Use the minimality of old_rem@[mi] and distinctness of old_rem to conclude strict inequality
            assert(forall|k: int| 0 <= k < old_rem.len() && k != mi ==> old_rem@[mi] < old_rem@[k]);
            // Combine to get the desired result
            assert(forall|y: i32| rem@.contains(y) ==> mv < y);
        }
    }

    // At this point rem is empty and result contains all elements of initial (distinct elements of s), in strictly increasing order.
    result
    // impl-end
}
// </vc-code>

fn main() {}
}