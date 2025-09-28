// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert i8 to int */
spec fn i8_to_int(x: i8) -> int {
    x as int
}
// </vc-helpers>

// <vc-spec>
fn around(a: Vec<i8>, decimals: i8) -> (result: Vec<i8>)
    requires decimals as int == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] as int == 0 ==> result[i] as int == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] as int <= a[j] as int ==> result[i] as int <= result[j] as int,

        forall|i: int| 0 <= i < a.len() ==>
            result[i] as int - 1 <= a[i] as int && a[i] as int <= result[i] as int + 1,

        forall|i: int| 0 <= i < a.len() && a[i] as int >= 0 ==> result[i] as int >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): copy input vector element-wise preserving equality invariant with int indexing */
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> result[k] as int == a[k] as int,
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}