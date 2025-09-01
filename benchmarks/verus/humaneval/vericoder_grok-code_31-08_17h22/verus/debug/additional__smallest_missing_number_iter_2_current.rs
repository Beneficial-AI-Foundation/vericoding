use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
{
    if s.is_empty() {
        return 0;
    }
    let mut candidate: i32 = 0;
    let mut i: usize = 0;

    loop
        invariant
            0 <= candidate,
            i <= s.len(),
            forall|j: usize| j < i ==> s[j] < candidate,
            forall|k: int| 0 <= k < candidate ==> exists|j: usize| j < i && s[j] == k,
            cand_idate <= i as i32,
    {
        if i == s.len() {
            break;
        }
        if s[i] > candidate {
            break;
        } else if s[i] == candidate {
            candidate += 1;
        } else {
            // s[i] < candidate, but since sorted and previous checks, shouldn't happen
            assert(false);
        }
        i += 1;
    }
    candidate
}
// </vc-code>

fn main() {}
}