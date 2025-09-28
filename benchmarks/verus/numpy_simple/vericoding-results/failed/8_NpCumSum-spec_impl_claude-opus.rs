// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            i > 0 ==> sum == result[(i - 1) as int],
            forall|j: int| 0 <= j < i && j > 0 ==> result[j] as int == result[(j - 1) as int] as int + a[j] as int,
            i > 0 ==> result[0] == a[0],
        decreases a.len() - i
    {
        sum = if i == 0 { a[0] } else { sum + a[i] };
        result.push(sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}