// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, section is empty */
// </vc-helpers>

// <vc-spec>
fn numpy_rfftfreq(n: usize, d: i8) -> (result: Vec<i8>)
    requires 
        n > 0,
        d > 0,
    ensures
        result.len() == n / 2 + 1,
        result@[0] == 0,
        forall|i: int| 0 <= i < result.len() ==> result@[i] == i / ((d as int) * (n as int)),
        result@[(n / 2) as int] == (n / 2) as int / ((d as int) * (n as int)),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result@[i] <= result@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use concrete types like i32 for exec calculations to avoid Verus 'int' usage errors */
{
    let mut result: Vec<i8> = Vec::new();
    let den: i32 = (d as i32) * (n as i32);
    let mut i: usize = 0;
    while i <= n / 2
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == j / ((d as int) * (n as int)),
        decreases (n - i) as int
    {
        let val: i32 = if den != 0 { (i as i32) / den } else { 0 };
        proof {
            assert(val as int == (i as int) / ((d as int) * (n as int)));
        }
        result.push(val as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}