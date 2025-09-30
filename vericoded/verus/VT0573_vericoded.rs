// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique(ar: Vec<i8>) -> (result: (usize, Vec<i8>))
    ensures
        result.1.len() <= ar.len(),

        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i as int] as int <= result.1[j as int] as int,

        forall|i: int, j: int| 0 <= i < result.1.len() && 0 <= j < result.1.len() && i != j ==> result.1[i as int] != result.1[j as int],
// </vc-spec>
// <vc-code>
{
    let v: Vec<i8> = Vec::new();
    let n: usize = v.len();
    (n, v)
}
// </vc-code>

}
fn main() {}