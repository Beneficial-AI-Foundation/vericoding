// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i <= n / 2
        invariant
            i <= n / 2 + 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == j / ((d as int) * (n as int)),
            i > 0 ==> result@[0] == 0,
            forall|j: int, k: int| 0 <= j <= k < i ==> result@[j] <= result@[k],
        decreases n / 2 + 1 - i
    {
        let freq = (i as i8) / ((d as i8) * (n as i8));
        result.push(freq);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}