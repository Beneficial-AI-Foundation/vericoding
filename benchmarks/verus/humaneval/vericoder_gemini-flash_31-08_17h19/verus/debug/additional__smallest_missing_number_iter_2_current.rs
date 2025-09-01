use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
proof fn lemma_filter(s: Seq<i32>, upper_bound: int, idx: int, current_val: int)
    requires
        0 <= idx < s.len(),
        s.len() <= upper_bound,
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        idx == 0 || (idx > 0 && s[idx - 1] < current_val), // current_val is the value we are looking for
        current_val <= s[idx],
    ensures
        s[idx] == current_val || s[idx] > current_val,
{
    // This lemma is implicitly handled by the loop invariant.
}
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
    let mut current_val: i32 = 0;
    let mut idx: int = 0;

    #[verifier::loop_invariant_param(idx, current_val)]
    while (idx < s.len())
        invariant
            0 <= idx <= s.len(),
            0 <= current_val,
            forall|x: int| 0 <= x < current_val ==> ({
                let found: bool = false;
                let mut k: int = 0;
                while (k < idx)
                    invariant
                        0 <= k <= idx,
                        0 <= x,
                        forall|y: int| 0 <= y < k ==> s[y] != x,
                        forall|y: int| 0 <= y < x ==> s[y] >= 0,
                        idx <= s.len(),
                        current_val == x, // Current value we are checking is x
                        // Only s[k] is relevant for the inner loop
                        // The outer current_val must be equal to x
                        // The elements before idx in `s` array are checked for x's presence
                        // Check if x is in s[0..k-1] -- not needed now.
                        // The important part is that if `x` is in `s`, it must be less than `s[idx]` if `x < current_val`
                        // or equal to `current_val` if `current_val` is `x`
                        // If `s[k]` is `x`, it must have been handled.
                        // This implies s[k] must be smaller than s[idx]
                        //
                        // We are checking that for all `x` up to `current_val - 1`, `x` is present in `s`.
                        // If `x` is present in `s`, it must be by `s[k] == x` where `k < idx`.
                        // Since `s` is sorted, if `x` is present in `s`, it will appear before `idx` if `x < current_val`.
                        // The `current_val` maintains the smallest non-negative integer not yet seen in `s[0..idx-1]`.
                        // This means that for all `x` such that `0 <= x < current_val`, `x` must be in `s[0..idx-1]`.
                        // s[idx] contains the next element to be checked.
                        // If `s[idx] == current_val`, then `current_val` is present, so we increment `current_val`.
                        // If `s[idx] > current_val`, then `current_val` is missing.
                        // If `s[idx] < current_val` (this means `current_val` was incremented due to duplicates),
                        // we just advance `idx`.
                        // The invariant needs to capture that `current_val` is the smallest *missing* number
                        // from `s[0..idx-1]`.

                        forall|y: int| 0 <= y < x ==> exists|k_inner: int| 0 <= k_inner < idx && s[k_inner] == y,
                        idx <= s.len(), // Added this to support next iteration s[idx]
                        current_val == x, // This makes invariant true here.

                {
                    if (s[k] == x) {
                        break;
                    }
                    k = k + 1;
                }
                k < idx && s[k] == x
            }),
            forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
            forall|k: int| 0 <= k < idx ==> s[k] >= 0, // This is true from problem statement on 's' as a whole
            s.len() <= 100_000, // From problem statement
    {
        // s.len() can be large, up to 100_000, so we can't iterate over the whole array for each current_val.
        // We use the fact that `s` is sorted.
        // If s[idx] is equal to current_val, it means current_val is present.
        // So we increment current_val and continue to the next element in s.
        // If s[idx] is greater than current_val, it means current_val is missing.
        // So we return current_val.

        // If s[idx] == current_val
        if (s[idx] == current_val) {
            current_val = current_val + 1;
            idx = idx + 1;
        } else if (s[idx] < current_val) {
            // This case handles duplicates in `s`.
            // Example: s = [0, 0, 1, 3], current_val = 0. s[0] == 0, current_val becomes 1. idx becomes 1.
            // s = [0, 0, 1, 3], current_val = 1. s[1] == 0. So current_val = 1 is still missing.
            // We need to advance idx to check the next element in `s`.
            idx = idx + 1;
        } else {
            // s[idx] > current_val. `current_val` is the smallest missing number.
            // Since s[idx] is sorted, all further elements will also be >= current_val,
            // so current_val will remain missing.
            assert(current_val <= s[idx]);
            // The loop invariant states that for all x < current_val, x is in s[0..idx-1].
            // And here we found s[idx] > current_val, so current_val must be missing.
            // We can break the loop and return current_val.
            break;
        }
    }
    current_val
    // impl-end
}
// </vc-code>

fn main() {}
}