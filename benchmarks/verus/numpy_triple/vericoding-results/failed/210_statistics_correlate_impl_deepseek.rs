// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed decreases clause to use local variable i */
spec fn correlation_sum_nonrec(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum_nonrec(a, v.skip(1), k + 1)
    }
}

proof fn correlation_sum_lemma(a: Seq<i32>, v: Seq<i32>, k: int)
    ensures
        correlation_sum(a, v, k) == correlation_sum_nonrec(a, v, k),
    decreases v.len()
{
    if v.len() > 0 {
        correlation_sum_lemma(a, v.skip(1), k + 1);
    }
}

fn compute_kth_correlation(a: &Vec<i32>, v: &Vec<i32>, k: usize) -> (result: i32)
    requires
        k < a.len() - v.len() + 1,
        v@.len() > 0,
        v@.len() <= a@.len(),
    ensures
        result == correlation_sum(a@, v@, k as int),
    decreases v.len() - i
{
    proof {
        correlation_sum_lemma(a@, v@, k as int);
    }
    
    let mut sum = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == correlation_sum_nonrec(a@, v@.take(i as int), k as int),
        decreases v.len() - i
    {
        sum = sum + a[k + i] * v[i];
        i = i + 1;
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
/* code modified by LLM (iteration 5): Fixed while loop invariant */
{
    let mut result = Vec::with_capacity(a.len() - v.len() + 1);
    let mut k: usize = 0;
    
    while k < a.len() - v.len() + 1
        invariant
            0 <= k <= a.len() - v.len() + 1,
            result.len() == k,
            forall|i: int| 0 <= i < k as int ==> result@[i] == correlation_sum(a@, v@, i),
        decreases (a.len() - v.len() + 1) - k
    {
        let value = compute_kth_correlation(&a, &v, k);
        result.push(value);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}