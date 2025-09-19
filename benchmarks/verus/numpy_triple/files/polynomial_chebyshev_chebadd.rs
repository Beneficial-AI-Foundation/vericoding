// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() {
                result[i] as int == c1[i] as int
            } else if i < c2.len() {
                result[i] as int == c2[i] as int
            } else {
                result[i] as int == 0
            }
        },
        forall|i: int| 0 <= i < c1@.len() ==> c1[i] != 0 ==> {
            exists|j: int| 0 <= j < result@.len() && j == i && {
                if i < c2@.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] as int == c1[i] as int
                }
            }
        },
        forall|i: int| 0 <= i < c2@.len() ==> c2[i] != 0 ==> {
            exists|j: int| 0 <= j < result@.len() && j == i && {
                if i < c1@.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] as int == c2[i] as int
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}