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
            rem.push(x);
            proof {
                // witness is i
                assert(rem@.contains(x));
                assert(exists|k: int| 0 <= k < i + 1 && s@[k] == x);
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

        // Work with a snapshot old_rem to find minimal element and construct new_rem without relying on Vec::remove
        let old_rem: Vec<i32> = rem.clone();
        let mi = min_index(&old_rem);
        assert(0 <= mi && mi < old_rem.len());
        let mv = old_rem@[mi];
        assert(initial@.contains(mv));

        // Build new_rem = old_rem with index mi removed
        let mut new_rem: Vec<i32> = Vec::new();
        let mut j: int = 0;
        while j < old_rem.len() {
            invariant 0 <= j && j <= old_rem.len();
            invariant forall|t: i32| new_rem@.contains(t) ==> exists|k: int| 0 <= k < j && k != mi && old_rem@[k] == t;
            invariant forall|k: int| 0 <= k < j && k != mi ==> new_rem@.contains(old_rem@[k]);
            invariant forall|p: int, q: int| 0 <= p < q < new_rem.len() ==> new_rem@[p] != new_rem@[q];
            invariant new_rem.len() == if j <= mi { j } else { j - 1 };
            if j != mi {
                new_rem.push(old_rem@[j]);
            }
            j += 1;
        }
        // After the loop, new_rem is old_rem without the element at mi
        proof {
            // new_rem contains exactly those elements of old_rem at indices k != mi
            assert(new_rem.len() == old_rem.len() - 1);
            assert(forall|y: i32| new_rem@.contains(y) ==> old_rem@.contains(y));
            assert(forall|y: i32| old_rem@.contains(y) && (y != mv) ==> new_rem@.contains(y));
            // since old_rem had distinct elements, new_rem also has distinct elements
            assert(forall|p: int, q: int| 0 <= p < q < new_rem.len() ==> new_rem@[p] != new_rem@[q]);
        }

        // Update rem to new_rem
        rem = new_rem;

        // Push mv onto result; must show new sortedness and invariants preserved.
        // If result was non-empty, its last element < mv by invariant, so ordering preserved.
        result.push(mv);

        proof {
            // Show mv is not in rem and mv is smaller than every element in rem.
            assert(!rem@.contains(mv));
            // For any y in rem, y is from old_rem with index != mi, and old_rem@[mi] <= old_rem@[k] with distinctness implies strict <
            assert(forall|k: int| 0 <= k < old_rem.len() && k != mi ==> old_rem@[mi] < old_rem@[k]);
            assert(forall|y: i32| rem@.contains(y) ==> exists|k: int| 0 <= k < old_rem.len() && k != mi && old_rem@[k] == y);
            assert(forall|y: i32| rem@.contains(y) ==> mv < y);
            // Show ordering of result remains strictly increasing
            if result.len() > 1 {
                let last_idx = result.len() - 1;
                // previous last < mv by loop invariant; mv < any element in rem by above, so new invariant holds
                assert(result@[last_idx - 1] < result@[last_idx]);
            }
            // result elements are from initial
            assert(initial@.contains(result@[result.len() - 1]));
        }
    }

    // At this point rem is empty and result contains all elements of initial (distinct elements of s), in strictly increasing order.
    result
}
// </vc-code>

fn main() {}
}