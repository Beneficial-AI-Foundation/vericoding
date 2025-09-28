// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type cast in loop invariant */
{
    let mut result_vec: Vec<i8> = Vec::with_capacity(a.len());
    if a.len() == 0 {
        return result_vec;
    }

    result_vec.push(a[0]);
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            // Ensure previous elements in result_vec are correct
            forall|j: int| 0 < j < i ==> result_vec[j] as int == result_vec[j as usize -1] as int + a[j as usize] as int,
            // Ensure the first element is correctly initialized
            result_vec.len() > 0 ==> result_vec[0] as int == a[0] as int,
        decreases a.len() - i
    {
        // Calculate the next cumulative sum and push it to the result vector
        result_vec.push((result_vec[i as usize -1] as i8 + a[i as usize] as i8) as i8);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}