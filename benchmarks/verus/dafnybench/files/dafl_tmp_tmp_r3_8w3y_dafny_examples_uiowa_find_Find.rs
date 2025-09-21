// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i8>, key: i8) -> (i: i8)
    ensures

        0 <= i ==> (
                    (i as int) < a@.len() && 

                    a@[i as int] == (key as int) && 

                    forall|k: int| 0 <= k < (i as int) ==> a@[k] != (key as int)
                   ),

        i < 0 ==> 

                forall|k: int| 0 <= k < a@.len() ==> a@[k] != (key as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}