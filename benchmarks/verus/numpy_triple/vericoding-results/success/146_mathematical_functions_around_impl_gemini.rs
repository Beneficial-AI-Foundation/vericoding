// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == a[j] as int,
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