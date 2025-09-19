// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn second_smallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn second_smallest(s: &Vec<i32>) -> i32
    recommends second_smallest_precond(s),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}

spec fn second_smallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == result) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < result &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}

proof fn second_smallest_spec_satisfied(s: &Vec<i32>)
    requires second_smallest_precond(s)
    ensures second_smallest_postcond(s, second_smallest(s))
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {}