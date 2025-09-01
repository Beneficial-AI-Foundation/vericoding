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
    let mut present: Vec<bool> = Vec::from_seq(Seq::repeat(false, (n + 1) as nat));

    // Scan `s` and mark presence of values in range [0, n].
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant present.len() as int == n + 1
        invariant
            forall|k: int|
                0 <= k <= n ==>
                    (present@[k as nat] ==> exists|j: int| 0 <= j < i && s[j] == k as i32)
        invariant
            forall|k: int|
                0 <= k <= n ==>
                    ((exists|j: int| 0 <= j < i && s[j] == k as i32) ==> present@[k as nat])
    {
        let x: i32 = s[i];
        if 0 <= x && x as int <= n {
            // mark presence
            present.set(x as nat, true);
        }
        i += 1;
    }

    // Find the smallest index in [0, n] that is not present.
    let mut k: int = 0;
    while k <= n
        invariant 0 <= k && k <= n + 1
        invariant present.len() as int == n + 1
        invariant forall|t: int| 0 <= t < k ==> present@[t as nat]
    {
        if !present@[k as nat] {
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

        assert(present.len() as int == n + 1);

        // From the scanning invariants (with i == n) we have the equivalence:
        assert(
            forall|q: int|
                0 <= q <= n ==>
                    (present@[q as nat] ==> exists|j: int| 0 <= j < n && s[j] == q as i32)
        );
        assert(
            forall|q: int|
                0 <= q <= n ==>
                    ((exists|j: int| 0 <= j < n && s[j] == q as i32) ==> present@[q as nat])
        );

        // There must exist some q in 0..=n with !present[q] (pigeonhole principle),
        // which ensures the loop above breaks with k <= n. We can therefore assert:
        assert(0 <= k && k <= n);

        // Now, since present[k] == false, there is no j with s[j] == k.
        assert(!present@[k as nat]);
        assert(!(exists|j: int| 0 <= j < n && s[j] == k as i32));

        // So forall i: 0 <= i < n ==> s[i] != v
        assert(forall|idx: int| 0 <= idx < n ==> s[idx] != v);

        // For all m: 0 <= m < v && s[m] != v ==> exists j . s[j] == m
        // Since k is the first index with present[k] == false, for all t < k we have present[t] == true.
        assert(forall|m: int|
            0 <= m < k ==>
                (present@[m as nat] && (exists|j: int| 0 <= j < n && s[j] == m as i32))
        );
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