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
    /* code modified by LLM (iteration 5): fixed type consistency by casting to i32 consistently */
    let mut result = Vec::new();
    let mut cumulative_sum: i32 = 0;
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> {
                let expected = if j == 0 { a[0] as i32 } else { (result[(j-1) as int] as i32 + a[j as int] as i32) as i32 };
                result[j as int] as i32 == expected
            },
            i > 0 ==> cumulative_sum == result[(i-1) as int] as i32
    {
        if i == 0 {
            cumulative_sum = a[0] as i32;
        } else {
            cumulative_sum = cumulative_sum + a[i] as i32;
        }
        result.push(cumulative_sum as i8);
    }
    
    result
}
// </vc-code>


}
fn main() {}