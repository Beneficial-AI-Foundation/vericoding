// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            0 <= i as int && i as int <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j] == a[j],
        decreases n as int - i as int
    {
        let x = a[i];
        result.push(x);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}