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
{
    let len = s.len();
    let mut v = 0;
    for i in 0..len {
        loop invariant i <= len;
        loop invariant v == i;
        loop invariant (forall |j: nat| #[trigger] 0 <= j < i ==> s[j] == j);
        if s[i] != v {
            return v;
        }
        v = v + 1;
    }
    v
}
// </vc-code>

fn main() {}
}