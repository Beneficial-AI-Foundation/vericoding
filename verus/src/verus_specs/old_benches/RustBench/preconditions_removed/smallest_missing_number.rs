use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
