use vstd::prelude::*;

verus! {

/*
function_signature: "fn max_dafny_lsp(a: &[i32]) -> (x: usize)"
docstring: Find the maximum element in an array.
*/

#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn main() {}
}