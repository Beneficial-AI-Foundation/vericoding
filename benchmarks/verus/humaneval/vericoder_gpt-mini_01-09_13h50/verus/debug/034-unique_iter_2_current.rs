use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: usize = s.len();
    let nn: int = n as int;
    let mut used: Vec<bool> = Vec::from_iter((0..n).map(|_| false));
    let mut result: Vec<i32> = vec![];

    // Outer loop: while there exists an index not yet used
    while (exists(|i: int| 0 <= i && i < nn && !used[i as usize])) {
        invariant used.len() == n;
        invariant result.len() <= n;
        invariant forall |i: int| 0 <= i && i < nn ==>
            (used[i as usize] ==> result@.contains(s[i as usize]));
        invariant forall |i: int| 0 <= i && i < nn ==>
            (!used[i as usize] ==> (result.len() == 0 || s[i as usize] > result[result.len() - 1]));
        invariant forall |p: int, q: int| 0 <= p && p < q && q < (result.len() as int) ==>
            result[p as usize] < result[q as usize];
        invariant forall |p: int| 0 <= p && p < (result.len() as int) ==>
            (exists(|j: int| 0 <= j && j < nn && s[j as usize] == result[p as usize]));
        decreases nn - (result.len() as int);

        // find first not-used index
        let mut min_idx: usize = 0usize;
        // ensure min_idx starts at a not-used index (scan until not-used)
        while used[min_idx] {
            invariant 0 <= (min_idx as int) && (min_idx as int) < nn;
            invariant exists(|k: int| (min_idx as int) <= k && k < nn && !used[k as usize]);
            decreases nn - (min_idx as int);
            min_idx += 1;
        }

        // now min_idx is some not-used index; scan to find minimal value among not-used
        let start: usize = min_idx;
        let mut j: usize = start + 1;
        while j < n {
            invariant 0 <= (start as int) && (start as int) < nn;
            invariant start < n;
            invariant start <= min_idx && min_idx < n;
            // min_idx is always a not-used index and its value is <= any checked not-used before j
            invariant !used[min_idx];
            invariant forall |t: int| (start as int) <= t && t < (j as int) ==>
                (!used[t as usize] ==> s[min_idx] <= s[t as usize]);
            decreases (n as int) - (j as int);
            if !used[j] && s[j] < s[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        // min_idx now holds index of minimal value among not-used indices
        let v: i32 = s[min_idx];

        // push v to result
        result.push(v);

        // mark all indices equal to v as used
        let mut k: usize = 0;
        while k < n {
            invariant 0 <= (k as int) && (k as int) <= nn;
            invariant forall |t: int| 0 <= t && t < (k as int) ==>
                (used[t as usize] || (exists(|u: int| 0 <= u && u < nn && s[u as usize] == result[(result.len() - 1)] && used[u as usize])));
            decreases (n as int) - (k as int);
            if !used[k] && s[k] == v {
                used[k] = true;
            }
            k += 1;
        }

        // after marking, every remaining not-used element must be > v (the minimal among previous not-used)
        assert(forall |i: int| 0 <= i && i < nn ==>
            (!used[i as usize] ==> s[i as usize] > result[result.len() - 1]));
    }

    // At termination, all indices are used, so every s[i] is contained in result
    assert(forall |i: int| 0 <= i && i < nn ==> result@.contains(s[i as usize]));

    // Return the result
    result
    // impl-end
}
// </vc-code>

fn main() {}
}