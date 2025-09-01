use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut candidate: int = 0;
    let mut i: usize = 0;

    loop
        invariant
            0 <= candidate,
            i <= s.len(),
            candidate <= i + 1,
            forall|j: usize| j < i ==> s@[j as int] < candidate,
            forall|k: int| 0 <= k < candidate ==> exists|j: usize| j < i && s@[j as int] == k,
    {
        if i == s.len() {
            break;
        }
        if s@[i as int] > candidate {
            break;
        } else if s@[i as int] == candidate {
            candidate += 1;
        } else if s@[i as int] < candidate {
            // skip this element
        }
        i += 1;
    }
    assert(candidate <= 100001 as int);
    assert(candidate >= 0);
    (candidate as i32)
}
// </vc-code>

fn main() {}
}