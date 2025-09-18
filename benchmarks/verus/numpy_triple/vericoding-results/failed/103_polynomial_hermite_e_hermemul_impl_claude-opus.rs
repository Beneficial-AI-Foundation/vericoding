// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || 
        (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0) 
        ==> (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix arithmetic overflow and precondition errors */
    let n = c1.len();
    let m = c2.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n + m - 1
        invariant
            i <= n + m - 1,
            result.len() == i,
            n == c1.len(),
            m == c2.len(),
            n > 0,
            m > 0,
            n + m >= 1,
        decreases (n + m - 1) - i
    {
        let mut sum: f64 = 0.0;
        let mut j: usize = if i >= m - 1 { i - (m - 1) } else { 0 };
        while j <= i && j < n
            invariant
                j <= i + 1,
                j <= n,
                i < n + m - 1,
                n == c1.len(),
                m == c2.len(),
            decreases n - j
        {
            if i >= j && (i - j) < m {
                sum = sum + c1[j] * c2[i - j];
            }
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