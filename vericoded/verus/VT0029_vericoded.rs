// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_one_positive()
    ensures
        1i8 as int > 0,
{
}

// </vc-helpers>

// <vc-spec>
fn ones(n: usize) -> (result: Vec<i8>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] as int == 1,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],
        forall|i: int| 0 <= i < n ==> result[i] as int > 0,
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
            forall|k: int| 0 <= k < i as int ==> v@[k] == 1i8,
        decreases n - i
    {
        v.push(1i8);
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}