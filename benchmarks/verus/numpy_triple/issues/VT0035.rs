// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == 0,
        forall|v: Vec<i32>, i: int| 
            v.len() == n && 0 <= i < n ==> 
            result[i] + v[i] == v[i] && v[i] + result[i] == v[i],
        forall|scalar: i32, i: int| 
            0 <= i < n ==> scalar * result[i] == 0,
        forall|v: Vec<i32>, i: int| 
            v.len() == n && 0 <= i < n ==> result[i] * v[i] == 0,
        n > 0 ==> result[0] == 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}