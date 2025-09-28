// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed integer literal syntax by removing 'int' suffix */
fn correlation_sum_take_equiv(a: Seq<i32>, v: Seq<i32>, k: int, j: int)
    requires
        0 <= j <= v.len(),
        0 <= k,
        k + j <= a.len(),
    ensures
        correlation_sum(a, v.take(j), k) == correlation_sum_iter(a, v, k, j),
    decreases j
{
    if j == 0 {
        assert(v.take(0).len() == 0);
    } else {
        correlation_sum_take_equiv(a, v, k, j - 1);
        assert(v.take(j) == v.take(j - 1).push(v[j - 1]));
    }
}

spec fn correlation_sum_iter(a: Seq<i32>, v: Seq<i32>, k: int, j: int) -> int
    requires
        0 <= j <= v.len(),
        0 <= k,
{
    if j == 0 {
        0
    } else {
        correlation_sum_iter(a, v, k, j - 1) + a[k + j - 1] * v[j - 1]
    }
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
{
    /* code modified by LLM (iteration 5): removed proof block usage of lemma */
    let mut result = Vec::new();
    let n = a.len();
    let m = v.len();
    
    if n + 1 < m {
        return result;
    }
    
    for k in 0..(n + 1 - m)
        invariant
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result[i] == correlation_sum(a@, v@, i),
            n + 1 >= m,
            k <= n + 1 - m,
    {
        let mut sum = 0;
        
        for j in 0..m
            invariant
                0 <= j <= m,
                sum == correlation_sum_iter(a@, v@, k as int, j as int),
                k + m <= a.len(),
        {
            sum += a[k + j] * v[j];
        }
        
        result.push(sum);
    }
    
    result
}
// </vc-code>


}
fn main() {}