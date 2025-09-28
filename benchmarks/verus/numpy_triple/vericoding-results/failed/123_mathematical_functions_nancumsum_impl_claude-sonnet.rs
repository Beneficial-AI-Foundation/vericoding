// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax */
lemma lemma_wrapping_add_correct(x: i8, y: i8)
    ensures
        x.wrapping_add(y) as int == ((x as int + y as int) % 256 + 256) % 256,
{
}
// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant to match postcondition exactly */
    let mut result = Vec::new();
    if a.len() == 0 {
        return result;
    }
    
    result.push(a[0]);
    
    let mut i = 1;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            i > 0,
            result[0] as int == a[0] as int,
            forall|j: int| 0 < j < i ==> result[j] as int == result[j-1] as int + a[j] as int,
        decreases a.len() - i
    {
        let sum = (result[i-1] as int + a[i] as int) as i8;
        result.push(sum);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}