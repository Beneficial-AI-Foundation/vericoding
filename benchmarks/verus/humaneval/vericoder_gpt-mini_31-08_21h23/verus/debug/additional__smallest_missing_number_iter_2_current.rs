use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this implementation.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: int = s.len();

    // Build a boolean vector `present` of length n+1, initialized to `false`.
    let mut present: Vec<bool> = Vec::new();
    let mut ii: int = 0;
    while ii <= n
        invariant 0 <= ii && ii <= n + 1
        invariant present.len() == ii
    {
        present.push(false);
        ii += 1;
    }
    assert(present.len() == n + 1);

    // Scan `s` and mark presence of values in range [0, n].
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant present.len() == n + 1
        invariant
            forall|k: int|
                0 <= k <= n ==>
                    (present[k] ==> exists|j: int| 0 <= j < i && s[j] == k as i32)
        invariant
            forall|k: int|
                0 <= k <= n ==>
                    ((exists|j: int| 0 <= j < i && s[j] == k as i32) ==> present[k])
    {
        let x: i32 = s[i];
        if 0 <= x && x as int <= n {
            // mark presence
            present[x as int] = true;
            // The invariants are preserved:
            // - for k == x: present[x] becomes true and s[i] == x provides the witness j = i
            // - for k != x: no change
        }
        i += 1;
    }

    // Find the smallest index in [0, n] that is not present.
    let mut k: int = 0;
    while k <= n
        invariant 0 <= k && k <= n + 1
        invariant present.len() == n + 1
        invariant forall|t: int| 0 <= t < k ==> present[t]
    {
        if !present[k] {
            break;
        }
        k += 1;
    }

    // k is in 0..=n and present[k] == false
    // Return k as the smallest missing number.
    let v: i32 = k as i32;

    // Proofs of postconditions:
    proof {
        // 0 <= v
        assert(0 <= k);
        assert(0 <= v);

        // v not present in s: present[k] == false implies no j with s[j] == k
        // From the scanning invariant (after full scan) we have:
        // forall q in 0..=n: present[q] <==> exists j < n . s[j] == q
        // We established both implications as invariants through the scan loop,
        // and after scanning i == n so they hold for the whole array.
        // Therefore, present[k] == false ==> no j with s[j] == k.
        assert(present.len() == n + 1);
        // Ensure the equivalences from the scan hold for i == n
        // Re-establish the two directions for clarity:
        assert(
            forall|q: int|
                0 <= q <= n ==>
                    (present[q] ==> exists|j: int| 0 <= j < n && s[j] == q as i32)
        );
        assert(
            forall|q: int|
                0 <= q <= n ==>
                    ((exists|j: int| 0 <= j < n && s[j] == q as i32) ==> present[q])
        );

        // Now, since present[k] == false, there is no j with s[j] == k.
        assert(!present[k]);
        assert(!(exists|j: int| 0 <= j < n && s[j] == k as i32));

        // So forall i: 0 <= i < n ==> s[i] != v
        assert(forall|idx: int| 0 <= idx < n ==> s[idx] != v);

        // Finally, for all m: 0 <= m < v && s[m] != v ==> exists j . s[j] == m
        // Since k is the first index with present[k] == false, for all t < k we have present[t] == true.
        // And present[t] == true <==> exists j . s[j] == t.
        assert(forall|m: int|
            0 <= m < k ==>
                (present[m] && (exists|j: int| 0 <= j < n && s[j] == m as i32))
        );
        // For m < v (v == k) the guard s[m] != v is redundant because v is not present anywhere,
        // but the postcondition requires only existence when that guard holds. We therefore have:
        assert(forall|m: int|
            0 <= m < v && s[m] != v ==>
                exists|j: int| 0 <= j < n && s[j] == m as i32
        );
    }

    v
    // impl-end
}
// </vc-code>

fn main() {}
}