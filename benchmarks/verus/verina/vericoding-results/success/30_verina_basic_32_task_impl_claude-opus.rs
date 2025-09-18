// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = a.len();
    
    if n == 1 {
        result.push(a[0]);
    } else {
        result.push(a[n - 1]);
        
        let mut i: usize = 1;
        while i < n - 1
            invariant
                1 <= i <= n - 1,
                n == a.len(),
                result.len() == i,
                result[0] == a[n - 1],
                forall|j: int| 1 <= j < i ==> result[j] == a[j],
            decreases n - 1 - i,
        {
            result.push(a[i]);
            i = i + 1;
        }
        
        result.push(a[0]);
    }
    
    result
}
// </vc-code>

}
fn main() {}