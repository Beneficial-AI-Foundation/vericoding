// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): deterministic arccos mapping for i8 in {-1,0,1} */
fn acos_map(xi: i8) -> (r: i8)
    ensures
        0 <= r as int && r as int <= 3,
        (xi as int == -1 ==> r as int == 3),
        (xi as int == 1 ==> r as int == 0),
{
    if xi == -1 { 3 } else if xi == 1 { 0 } else { 1 }
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
    /* code modified by LLM (iteration 2): build result by iterating and using helper; fix casting in assertions */
    let n = x.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> (
                0 <= result@[j] as int &&
                result@[j] as int <= 3 &&
                (x@[j] as int == -1 ==> result@[j] as int == 3) &&
                (x@[j] as int == 1 ==> result@[j] as int == 0)
            ),
        decreases n as int - i as int
    {
        let xi = x[i];
        let ri = acos_map(xi);
        let cur = i;
        result.push(ri);
        assert(result.len() == cur + 1);
        assert(result@[cur as int] == ri);
        proof {
            assert(cur < n);
            assert(x@[cur as int] == xi);
            let rj = result@[cur as int];
            assert(rj == ri);
            assert(0 <= rj as int && rj as int <= 3);
            if x@[cur as int] as int == -1 {
                assert(rj as int == 3);
            }
            if x@[cur as int] as int == 1 {
                assert(rj as int == 0);
            }
        }
        i = cur + 1;
    }
    result
}
// </vc-code>


}
fn main() {}