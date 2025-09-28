// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] as int == arr[i] as int * arr[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added overflow check and assertion to maintain invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == arr[j] as int * arr[j] as int,
        decreases arr.len() - i
    {
        let val = arr[i];
        let squared: i8 = if val as int * val as int > 127 {
            127
        } else if val as int * val as int < -128 {
            -128  
        } else {
            val * val
        };
        assert(result.len() == i);
        result.push(squared);
        assert(result.len() == i + 1);
        assert(result[i as int] as int == squared as int);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}