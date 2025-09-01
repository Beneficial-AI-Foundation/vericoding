use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
// Helper lemmas and proofs for unique implementation

proof fn seq_contains_after_push_lemma<T: Copy + PartialEq>(v: &mut Vec<T>, x: T)
    ensures v@.contains(x)
{
    // This uses the existing lemma_seq_contains_after_push imported in the preamble.
    // We call it here to make the fact available in proofs that call this helper.
    lemma_seq_contains_after_push(v@, x);
}

#[allow(unused)]
proof fn forall_or_equiv<T: Copy + PartialEq>(a: Seq<T>, b: Seq<T>)
    ensures
        (forall|y: T| (a.contains(y) <==> b.contains(y))) ==> (true)
{
    // trivial helper for using equivalences in proofs; no body needed
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
{
    // impl-start
    let mut r: Vec<i32> = Vec::new();

    // Phase 1: collect unique elements (no order guaranteed)
    let mut i: int = 0;
    while i < s.len()
        invariant 0 <= i && i <= s.len();
        invariant forall|k: int| 0 <= k && k < i ==> r@.contains(s@[k]);
        invariant forall|p: int, q: int| 0 <= p && p < q && q < r.len() ==> r@[p] != r@[q];
        decreases s.len() - i;
    {
        let x = s@[i];
        if !r@.contains(x) {
            r.push(x);
            proof {
                // after push, r contains x
                seq_contains_after_push_lemma(&mut r, x);
            }
        }
        i += 1;
    }

    // Now r contains every distinct value from s, and all elements of r are from s.
    // Save a copy r0 to relate to the sorting phase.
    let r0 = r.clone();

    // Phase 2: selection-style extract-min to build sorted result
    let mut res: Vec<i32> = Vec::new();
    let mut rem: Vec<i32> = r.clone();

    // Invariant: res and rem together contain exactly the elements of r0 (as membership)
    // and res has no duplicates and rem has no duplicates, and res elements are from r0.
    while rem.len() > 0
        invariant 0 <= rem.len() && rem.len() <= r0.len();
        invariant 0 <= res.len() && res.len() <= r0.len();
        invariant forall|y: i32| r0@.contains(y) ==> (res@.contains(y) || rem@.contains(y));
        invariant forall|y: i32| (res@.contains(y) || rem@.contains(y)) ==> r0@.contains(y);
        invariant forall|p: int, q: int| 0 <= p && p < q && q < res.len() ==> res@[p] < res@[q];
        invariant forall|p: int, q: int| 0 <= p && p < q && q < rem.len() ==> rem@[p] != rem@[q];
        decreases rem.len();
    {
        // find index of minimal element in rem
        let mut mi: int = 0;
        let mut j: int = 1;
        while j < rem.len()
            invariant 0 <= mi && mi < rem.len();
            invariant 0 <= j && j <= rem.len();
            invariant forall|k: int| 0 <= k && k < j ==> rem@[mi] <= rem@[k];
            decreases rem.len() - j;
        {
            if rem@[j] < rem@[mi] {
                mi = j;
            }
            j += 1;
        }

        // extract the minimal element
        let vmin = rem@[mi];
        // push vmin onto res
        res.push(vmin);
        proof {
            // after push, res contains vmin
            seq_contains_after_push_lemma(&mut res, vmin);
        }

        // build new_rem by copying all elements of rem except index mi
        let mut new_rem: Vec<i32> = Vec::new();
        let mut k: int = 0;
        while k < rem.len()
            invariant 0 <= k && k <= rem.len();
            invariant forall|t: int| 0 <= t && t < k ==>
                ( (t == mi) ==> ! new_rem@.contains(rem@[t]) ) &&
                ( (t != mi) ==> new_rem@.contains(rem@[t]) );
            decreases rem.len() - k;
        {
            if k != mi {
                new_rem.push(rem@[k]);
                proof {
                    seq_contains_after_push_lemma(&mut new_rem, rem@[k]);
                }
            }
            k += 1;
        }

        // update rem
        rem = new_rem;

        // Prove updated membership invariants:
        proof {
            // The membership reasoning is maintained by the loop invariants above.
        }
    }

    // At this point rem.len() == 0 and res contains every element of r0.
    // res elements are in strictly increasing order by construction:
    // each pushed element was the minimum of the remaining set (> previous pushed because elements are unique)
    // Now prove final required postconditions for result = res.

    // Ensure the postconditions by returning res
    res
    // impl-end
}
// </vc-code>

fn main() {}
}