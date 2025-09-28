// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn implies(p: bool, q: bool) -> bool {
    !p || q
}

proof fn bool_excluded_middle(b: bool)
    ensures
        b || !b,
{
}

proof fn implication_true(b: bool)
    ensures
        b ==> true,
{
}
// </vc-helpers>

// <vc-spec>
fn may_share_memory(a: &Vec<i8>, b: &Vec<i8>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (result == true ==> true) &&

        true &&

        true
// </vc-spec>
// <vc-code>
{
    false
}
// </vc-code>

}
fn main() {}