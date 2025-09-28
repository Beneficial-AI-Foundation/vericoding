// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn round_to_nearest(x: i8) -> i8
{
    x
}

/* helper modified by LLM (iteration 4): changed to spec function to avoid exec mode error */
proof fn monotonicity_preserved(a: Vec<i8>, result: Vec<i8>)
    requires
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == round_to_nearest(a[i]),
    ensures
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] as int <= a[j] as int ==> result[i] as int <= result[j] as int,
{
    assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] as int <= a[j] as int implies result[i] as int <= result[j] as int by {
        if 0 <= i < a.len() && 0 <= j < a.len() && a[i] as int <= a[j] as int {
            assert(result[i] == round_to_nearest(a[i]));
            assert(result[j] == round_to_nearest(a[j]));
            assert(result[i] as int <= result[j] as int);
        }
    };
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
    /* code modified by LLM (iteration 4): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == a[i],
            forall|i: int| 0 <= i < idx && a[i] as int == 0 ==> result[i] as int == 0,
            forall|i: int| 0 <= i < idx ==> result[i] as int - 1 <= a[i] as int && a[i] as int <= result[i] as int + 1,
            forall|i: int| 0 <= i < idx && a[i] as int >= 0 ==> result[i] as int >= 0,
            forall|i: int, j: int| 0 <= i < idx && 0 <= j < idx && a[i] as int <= a[j] as int ==> result[i] as int <= result[j] as int,
        decreases a.len() - idx
    {
        result.push(a[idx]);
        idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}