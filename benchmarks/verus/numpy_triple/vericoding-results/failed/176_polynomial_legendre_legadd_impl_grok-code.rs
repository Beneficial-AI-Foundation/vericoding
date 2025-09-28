// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
{
    let len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    for i in 0..len {
        let val1 = if i < c1.len() { c1[i] } else { 0i8 };
        let val2 = if i < c2.len() { c2[i] } else { 0i8 };
        result.push(val1 + val2);
    }
    result
}
// </vc-code>


}
fn main() {}