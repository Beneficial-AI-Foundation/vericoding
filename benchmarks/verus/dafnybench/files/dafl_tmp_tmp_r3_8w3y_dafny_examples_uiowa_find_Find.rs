// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (i: i32)
    ensures

        0 <= i ==> (
                    i < a.len() && 

                    a[i as int] == key && 

                    forall|k: int| 0 <= k < i ==> a[k] != key
                   ),

        i < 0 ==> 

                forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}