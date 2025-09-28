// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn arccos_value(x: i8) -> i8
    recommends -1 <= x <= 1
{
    if x == -1 {
        3
    } else if x == 0 {
        1
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn arccos(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            0 <= result[i] as int && 
            result[i] as int <= 3 &&
            (x[i] as int == -1 ==> result[i] as int == 3) &&
            (x[i] as int == 1 ==> result[i] as int == 0)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arccos_value(x[j]),
            forall|j: int| 0 <= j < i ==> 0 <= result[j] as int && result[j] as int <= 3,
            forall|j: int| 0 <= j < i ==> (x[j] as int == -1 ==> result[j] as int == 3),
            forall|j: int| 0 <= j < i ==> (x[j] as int == 1 ==> result[j] as int == 0),
        decreases x.len() - i
    {
        let val = if x[i] == -1 {
            3
        } else if x[i] == 0 {
            1
        } else {
            0
        };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}