// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<int>, input: Seq<char>) -> bool {
    result.len() >= 0 &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] >= 1) &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] <= result.len())
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<i8>)
    requires valid_input(input@)
    ensures valid_output(result@.map(|i: int, x: i8| x as int), input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Handle i8 range check before loop */
    let mut result: Vec<i8> = Vec::new();
    let n = input.len();
    
    if n == 0 {
        return result;
    }
    
    // Check if n fits in i8 range before proceeding
    if n > 127 {
        // Return empty vector if input is too large for i8
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 127,
            result@.len() == i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] >= 1,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] <= n as i8,
        decreases n - i
    {
        // Since we know n <= 127, we can safely cast to i8
        let value: i8 = (i + 1) as i8;
        result.push(value);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}