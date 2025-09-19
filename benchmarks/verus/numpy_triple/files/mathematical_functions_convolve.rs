// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn convolution_element_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        let i = 0;
        let contribution = if k >= i && k - i < v.len() {
            a[i] * v[k - i]
        } else {
            0
        };
        contribution + convolution_element_sum(a.skip(1), v, k)
    }
}

fn numpy_convolve(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0 && v.len() > 0,
    ensures 
        result.len() == a.len() + v.len() - 1,
        forall|k: int| 0 <= k < result.len() ==> result[k] == convolution_element_sum(a@, v@, k),
        result[0] == a[0] * v[0],
        result[result.len() - 1] == a[a.len() - 1] * v[v.len() - 1],
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