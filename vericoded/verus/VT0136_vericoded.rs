// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn equal_contents(a: Vec<i8>, b: Vec<i8>) -> bool
{
    a.len() == b.len() && a@ == b@
}

proof fn bool_is_bool(b: bool)
    ensures
        b == true || b == false,
{
}
// </vc-helpers>

// <vc-spec>
spec fn shares_memory(a: Vec<i8>, b: Vec<i8>) -> bool
{

    true &&

    (a.len() == b.len() && a@ == b@) &&

    true &&

    true
}

fn shares_memory_fn(a: Vec<i8>, b: Vec<i8>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (a.len() == b.len() && a@ == b@ ==> result == true) &&

        true
// </vc-spec>
// <vc-code>
{
    true
}
// </vc-code>

}
fn main() {}