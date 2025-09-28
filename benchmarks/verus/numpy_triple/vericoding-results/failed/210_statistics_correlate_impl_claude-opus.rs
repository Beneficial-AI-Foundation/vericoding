// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i <= a.len() - v.len()
        invariant
            i <= a.len() + 1 - v.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == correlation_sum(a@, v@, k),
        decreases a.len() - v.len() - i
    {
        let mut sum: i32 = 0;
        let mut j: usize = 0;
        while j < v.len()
            invariant
                j <= v.len(),
                sum == correlation_sum(a@, v@.take(j as int), i as int),
            decreases v.len() - j
        {
            sum = sum + a[i + j] * v[j];
            j = j + 1;
        }
        result.push(sum);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}