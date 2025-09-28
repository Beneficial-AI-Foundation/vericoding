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
    /* code modified by LLM (iteration 2): Added explicit type annotation to Vec::new() */
    let mut result: Vec<i8> = Vec::new();
    let n = input.len();
    
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] >= 1,
            forall|j: int| 0 <= j < i ==> result@[j] <= n,
    {
        result.push(1);
    }
    
    result
}
// </vc-code>


}

fn main() {}