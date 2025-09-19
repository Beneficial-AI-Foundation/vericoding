// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        c1@.len() > 0,
        c2@.len() > 0,
    ensures
        result@.len() == c1@.len() + c2@.len() - 1,
        (forall|i: int| 0 <= i < c1@.len() ==> c1@[i] as int == 0) || 
        (forall|j: int| 0 <= j < c2@.len() ==> c2@[j] as int == 0) 
        ==> (forall|k: int| 0 <= k < result@.len() ==> result@[k] as int == 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}