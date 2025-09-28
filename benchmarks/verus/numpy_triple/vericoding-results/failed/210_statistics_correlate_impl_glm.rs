// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed error by naming return value in function with ensures clause */
fn inner_product(a: &Vec<i32>, start: usize, v: &[i32]) -> (sum: i32)
    requires
        0 <= start < a.len(),
        start + v.len() <= a.len(),
    ensures
        sum == correlation_sum(a@, v@, start as int)
{
    let mut sum = 0;
    let mut i = 0;
    let n = v.len();
    while i < n
        invariant
            0 <= i <= n,
            sum == correlation_sum(a@, v@.subrange(0, i as int), start as int),
        decreases n - i
    {
        sum += a[start + i] * v[i];
        i += 1;
    }
    sum
}
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
/* code modified by LLM (iteration 5): no changes needed */
{
    let mut result = Vec::new();
    let n = a.len() - v.len() + 1;
    let mut k = 0;
    while k < n
        invariant
            0 <= k <= n,
            result.len() == k,
            forall|j: int| 0 <= j < k ==> result[j] == correlation_sum(a@, v@, j),
        decreases n - k
    {
        let s = inner_product(&a, k, &v);
        // The postcondition of inner_product ensures that s == correlation_sum(a@, v@, k)
        result.push(s);
        k += 1;
    }
    result
}
// </vc-code>


}
fn main() {}