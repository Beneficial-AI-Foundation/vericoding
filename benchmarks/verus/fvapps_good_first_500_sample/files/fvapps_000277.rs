// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bag_of_tokens_score(tokens: Vec<u32>, power: u32) -> (result: u32)
    requires 
        tokens.len() <= 1000,
        (forall|i: int| 0 <= i < tokens.len() ==> tokens[i] < 10000),
        power < 10000,
    ensures 
        result <= tokens.len(),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // let result1 = bag_of_tokens_score(vec![100], 50);
    // println!("{}", result1); // Should be 0

    // let result2 = bag_of_tokens_score(vec![100, 200], 150);
    // println!("{}", result2); // Should be 1

    // let result3 = bag_of_tokens_score(vec![100, 200, 300, 400], 200);
    // println!("{}", result3); // Should be 2
}