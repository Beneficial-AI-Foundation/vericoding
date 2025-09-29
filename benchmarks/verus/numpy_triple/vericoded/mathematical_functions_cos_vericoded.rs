// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_cos(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -1 <= result@[i] as int <= 1 &&
            (x@[i] as int == 0 ==> result@[i] as int == 1)
        }
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                -1 <= result@[j] as int <= 1 &&
                (x@[j] as int == 0 ==> result@[j] as int == 1)
            },
        decreases x.len() - i
    {
        let xi = x[i];
        let y: i8 = if xi == 0 { 1 } else { 0 };
        result.push(y);
        proof {
            assert(result@[i as int] == y);
            assert(-1 <= result@[i as int] as int);
            assert(result@[i as int] as int <= 1);
            assert(x@[i as int] == xi);
            if x@[i as int] as int == 0 {
                assert(xi == 0);
                assert(result@[i as int] as int == 1);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}