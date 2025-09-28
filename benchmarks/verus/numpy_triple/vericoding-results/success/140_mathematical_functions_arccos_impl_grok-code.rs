// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Fixed type mismatch in invariant by connecting conditions with && instead of commas forming a tuple */
    let mut result: Vec<i8> = Vec::new();
    for i in 0..x.len()
        invariant
            0 <= i as int <= x.len(),
            result.len() == i as int,
            forall |j: int| 0 <= j < i as int ==> 
                0 <= result[j] as int <= 3 &&
                (x[j] as int == -1 ==> result[j] as int == 3) &&
                (x[j] as int == 1 ==> result[j] as int == 0),
        decreases x.len() as int - i as int
    {
        let res: i8 = if x[i] == 1i8 {
            0i8
        } else if x[i] == -1i8 {
            3i8
        } else {
            1i8
        };
        result.push(res);
    }
    result
}
// </vc-code>


}
fn main() {}