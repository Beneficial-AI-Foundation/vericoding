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
    while (idx < s.len() as int)
        invariant
            0 <= idx <= s.len() as int,
            0 <= current_val,
            forall|x: int| 0 <= x < current_val ==> exists|k_inner: int| 0 <= k_inner < idx && s.spec_index(k_inner as nat) == x,
            forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
            forall|k: int| 0 <= k < s.len() ==> #[trigger] s.spec_index(k as nat) >= 0,
            s.len() <= 100_000,
    {
        proof {
            if s.spec_index(idx as nat) < current_val {
                assert(s.spec_index(idx as nat) >= 0); // From precondition
            }
        }
        if (s.spec_index(idx as nat) == current_val) {
            current_val = current_val + 1;
            idx = idx + 1;
        } else if (s.spec_index(idx as nat) < current_val) {
            idx = idx + 1;
        } else {
            assert(current_val <= s.spec_index(idx as nat)); // This holds by loop invariant and the 'else' condition
            break;
        }
    }
    current_val
    // impl-end
}
// </vc-code>

fn main() {}
}